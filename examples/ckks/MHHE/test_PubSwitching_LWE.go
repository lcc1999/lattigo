package main

import (
	"fmt"
	//"math"

	"github.com/tuneinsight/lattigo/v4/ckks"
	"github.com/tuneinsight/lattigo/v4/rlwe"
	//"github.com/tuneinsight/lattigo/v4/rlwe/ringqp"
	"github.com/tuneinsight/lattigo/v4/ring"
)


func reverse(s []uint64, start, end int) {
    for i, j := start, end; i < j; i, j = i+1, j-1 {
        s[i], s[j] = s[j], s[i]
    }
}

func genGenRotationKeys(params ckks.Parameters, sk *rlwe.SecretKey) *rlwe.RotationKeySet{
	kgen := ckks.NewKeyGenerator(params)
	rotations := params.GaloisElementsForTrace(0)//[]uint64{}
	for k:=1;k<=params.LogN();k++{
		var galEl uint64
		galEl = 1<<(params.LogN()-k+1)+1
		rotations = append(rotations, galEl)
	}

	rtks := kgen.GenRotationKeys(rotations,sk)
	return rtks
}



func getRLWEandLWEs(params ckks.Parameters, encryptor rlwe.Encryptor, logSlots int, values []float64) (*rlwe.Ciphertext, struct {a []byte; b [][]uint64}) {
	slots := 1 << logSlots
	if params.RingType() == ring.Standard  {
		slots <<= 1
	}
	level := params.MaxLevel()
	encoder := ckks.NewEncoder(params)
	plaintext := encoder.EncodeNew(values, level, params.DefaultScale(), logSlots)
	ciphertext := encryptor.EncryptNew(plaintext)
	
	var lwes struct {a []byte; b [][]uint64}
	lwes.b = make([][]uint64, slots)
	ringQ := params.RingQ()
	N := params.N()
	gap := N/slots


	ringQ.InvNTTLvl(ciphertext.Level(), ciphertext.Value[1], ciphertext.Value[1])
	ringQ.InvNTTLvl(ciphertext.Level(), ciphertext.Value[0], ciphertext.Value[0])
	lwes.a, _ = ciphertext.Value[1].MarshalBinary()
	for i, k:=0, 0;i<slots;i,k = i+1, k+gap {
		lwes.b[i]=make([]uint64,level+1)
		for j, _ := range ringQ.Modulus[:level+1]{
			lwes.b[i][j]= ciphertext.Value[0].Buff[j*N+k]
		}
	}
	ringQ.NTTLvl(ciphertext.Level(), ciphertext.Value[1], ciphertext.Value[1])
	ringQ.NTTLvl(ciphertext.Level(), ciphertext.Value[0], ciphertext.Value[0])
	return ciphertext, lwes
}

func preLWEtoRLWE(params ckks.Parameters, logSlots int, lwes struct {a []byte; b [][]uint64}) *rlwe.Ciphertext {
	N := params.N()
	level := params.MaxLevel()
	ringQ := params.RingQ()
	slots := 1 << logSlots
	if params.RingType() == ring.Standard  {
		slots <<= 1
	}

	gap := N/slots

	a := ringQ.NewPoly()
	b := ringQ.NewPoly()

	a.UnmarshalBinary(lwes.a)
	for j, _ := range ringQ.Modulus[:level+1]{
		for i, k:=0, 0;i<slots;i,k = i+1, k+gap {
			b.Buff[j*N+k]=lwes.b[i][j];
		}
		a.Coeffs[j]=a.Buff[j*N : (j+1)*N]
		b.Coeffs[j]=b.Buff[j*N : (j+1)*N]
	
		/*inv := ring.MForm(ring.ModExp(uint64(2<<logSlots), qj-2, qj), qj, ringQ.BredParams[j])
		ring.MulScalarMontgomeryVec(a.Coeffs[j][:N], a.Coeffs[j][:N], inv, qj, ringQ.MredParams[j])
		ring.MulScalarMontgomeryVec(b.Coeffs[j][:N], b.Coeffs[j][:N], inv, qj, ringQ.MredParams[j])*/
	}
	ciphertext := ckks.NewCiphertext(params, 1, level)
	ciphertext.Value[1] = a
	ciphertext.Value[0] = b
	ringQ.NTTLvl(ciphertext.Level(), ciphertext.Value[1], ciphertext.Value[1])
	ringQ.NTTLvl(ciphertext.Level(), ciphertext.Value[0], ciphertext.Value[0])

	return ciphertext
}

func EvalTrace(params ckks.Parameters, ciphertext *rlwe.Ciphertext, rtks *rlwe.RotationKeySet, logn int) *rlwe.Ciphertext {
	//ct := ckks.NewCiphertext(params, 1, params.MaxLevel())
	cipher := ciphertext
	evaluator := ckks.NewEvaluator(params, rlwe.EvaluationKey{Rtks:rtks})
	/*for k:=1;k<=params.LogN()-logn;k++{
		var galEl uint64
		galEl = 1<<(params.LogN()-k+1)+1
		//fmt.Println(galEl,params.InverseGaloisElement(galEl),params.RotationFromGaloisElement(params.InverseGaloisElement(galEl)))
		evaluator.GetRLWEEvaluator().Automorphism(cipher, galEl, ct)
		evaluator.Add(cipher,ct,cipher)
	}*/
	evaluator.Trace(cipher,logn,cipher)
	return cipher
}

func PackLWEs(params ckks.Parameters, ciphertexts []*rlwe.Ciphertext, l int, rtks *rlwe.RotationKeySet) *rlwe.Ciphertext {
	if l == 0 {
		return ciphertexts[0]
	}

	even := make([]*rlwe.Ciphertext,1<<(l-1));
	odd := make([]*rlwe.Ciphertext,1<<(l-1));
	for i:=0;i<1<<(l-1);i++{
		even[i]=ciphertexts[2*i]
		odd[i]=ciphertexts[2*i+1]
	}

	ct_even := PackLWEs(params, even, l-1, rtks)
	ct_odd := PackLWEs(params, odd, l-1, rtks)
	evaluator := ckks.NewEvaluator(params, rlwe.EvaluationKey{Rtks:rtks})
	encoder := ckks.NewEncoder(params)
	values := make([]float64, params.N())
	values[params.N()>>l]=1
	plaintext := encoder.EncodeCoeffsNew(values, params.MaxLevel(), rlwe.NewScale(1))
	ct := evaluator.MulNew(ct_odd, plaintext)

	c0 := evaluator.AddNew(ct_even,ct)
	c1 := evaluator.SubNew(ct_even,ct)
	var galEl uint64
	galEl = 1<<l+1
	evaluator.GetRLWEEvaluator().Automorphism(c1, galEl, c1)
	evaluator.Add(c0,c1,c0)
	return c0
}
func chebyshevinterpolation() {

	var err error

	params, err := ckks.NewParametersFromLiteral(ckks.PN14QP438)
	if err != nil {
		panic(err)
	}

	encoder := ckks.NewEncoder(params)

	kgen := ckks.NewKeyGenerator(params)
	sk, pk := kgen.GenKeyPair()

	rlk := kgen.GenRelinearizationKey(sk, 1)
	encryptor := ckks.NewEncryptor(params, pk)
	decryptor := ckks.NewDecryptor(params, sk)

	evaluator := ckks.NewEvaluator(params, rlwe.EvaluationKey{Rlk: rlk})

	values := make([]float64, params.Slots())


	fmt.Printf("CKKS parameters: logN = %d, logQ = %d, levels = %d, scale= %f, sigma = %f \n",
		params.LogN(), params.LogQP(), params.MaxLevel()+1, params.DefaultScale().Float64(), params.Sigma())


	fmt.Println(params.RingQ().Modulus[0])
	_=rlk
	logSlots := 2
	values = make([]float64, 1<<logSlots)
	values[0] =1
	values[1] =2
	values[2] =5
	values[3] =4

	clientcipher, lwes := getRLWEandLWEs(params, encryptor, logSlots, values)
	p:=decryptor.DecryptNew(clientcipher)

	ciphertext := preLWEtoRLWE(params, logSlots, lwes)


	newsk, newpk := kgen.GenKeyPair()
	swk := kgen.GenPubSwitchingKey(sk,newpk)
	decryptor = ckks.NewDecryptor(params, newsk)
	rtks := genGenRotationKeys(params, newsk)

	ciphertext=evaluator.SwitchKeysNew(ciphertext, swk)
	//rtks := genGenRotationKeys(params, sk)
	
	/*ciphertexts := make([]*rlwe.Ciphertext,len(lwes.b))
	for i:=0;i<len(lwes.b);i++{
		ciphertexts[i]=preLWEtoRLWE(params, logSlots, lwes, i)
	}

	ciphertext = PackLWEs(params, ciphertexts, logSlots+1, rtks)*/
	ciphertext = EvalTrace(params, ciphertext, rtks, logSlots)
	p=decryptor.DecryptNew(ciphertext)
	params.RingQ().InvNTTLvl(p.Level(), p.Value, p.Value)
	fmt.Println(p.Value.Buff[:10])
	params.RingQ().NTTLvl(p.Level(), p.Value, p.Value)

	fmt.Println(encoder.Decode(p, logSlots))

	ciphertext = evaluator.MulRelinNew(ciphertext,ciphertext )
	evaluator.Rescale(ciphertext,params.DefaultScale(),ciphertext )

	/*newsk, newpk := kgen.GenKeyPair()
	swk := kgen.GenPubSwitchingKey(sk,newpk)
	ct := evaluator.SwitchKeysNew(ciphertext, swk)
	decryptor = ckks.NewDecryptor(params, newsk)
	fmt.Println(encoder.Decode(decryptor.DecryptNew(ct), logSlots))*/
}


func main() {
	chebyshevinterpolation()
}
