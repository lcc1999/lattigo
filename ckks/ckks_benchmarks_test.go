package ckks

import (
	"fmt"
	"testing"
)

type benchParams struct {
	logN     uint64
	logQ     uint64
	levels   uint64
	logScale uint64
	sigma    float64
	bdc      uint64
}

func BenchmarkCKKSScheme(b *testing.B) {

	var err error
	var ckkscontext *CkksContext
	var encoder *Encoder
	var kgen *keygenerator
	var sk *SecretKey
	var pk *PublicKey
	var rlk *EvaluationKey
	var rotkey *RotationKey
	var encryptor *Encryptor
	var decryptor *Decryptor
	var evaluator *Evaluator
	var plaintext *Plaintext
	var ciphertext1 *Ciphertext
	var ciphertext2 *Ciphertext

	params := []benchParams{
		//{logN: 10, logQ: 30, levels:  1, logScale : 20, sigma: 3.19, bdc : 60},
		//{logN: 11, logQ: 60, levels:  1, logScale : 40, sigma: 3.19, bdc : 60},
		{logN: 12, logQ: 40, levels: 2, logScale: 40, sigma: 3.2, bdc: 60},
		{logN: 13, logQ: 40, levels: 4, logScale: 40, sigma: 3.2, bdc: 60},
		{logN: 14, logQ: 40, levels: 8, logScale: 40, sigma: 3.2, bdc: 60},
		{logN: 15, logQ: 40, levels: 16, logScale: 40, sigma: 3.2, bdc: 60},
	}

	var logN, logQ, logScale, levels, bdc uint64
	var sigma float64

	for _, param := range params {

		logN = param.logN
		logQ = param.logQ
		logScale = param.logScale
		levels = param.levels
		sigma = param.sigma
		bdc = param.bdc

		if ckkscontext, err = NewCkksContext(logN, logQ, logScale, levels, sigma); err != nil {
			b.Error(err)
		}

		encoder = ckkscontext.NewEncoder()

		kgen = ckkscontext.NewKeyGenerator()

		if sk, pk, err = kgen.NewKeyPair(); err != nil {
			b.Error(err)
		}

		if rlk, err = kgen.NewRelinKey(sk, bdc); err != nil {
			b.Error(err)
		}

		if rotkey, err = kgen.NewRotationKeysPow2(sk, bdc, true); err != nil {
			b.Error(err)
		}

		if encryptor, err = ckkscontext.NewEncryptor(pk, sk); err != nil {
			b.Error(err)
		}

		if decryptor, err = ckkscontext.NewDecryptor(sk); err != nil {
			b.Error(err)
		}

		evaluator = ckkscontext.NewEvaluator()

		_ = rotkey

		ciphertext1 = ckkscontext.NewCiphertext(1, levels-1, logScale)
		ciphertext2 = ckkscontext.NewCiphertext(1, levels-1, logScale)

		var values []complex128
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/Levels=%d/decomp=%d/sigma=%.2f/Encode", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			slots := 1 << (logN - 2)
			values = make([]complex128, slots)
			for i := 0; i < slots; i++ {
				values[i] = complex(randomFloat(0.1, 1), 0)
			}

			plaintext = ckkscontext.NewPlaintext(levels-1, logScale)

			for i := 0; i < b.N; i++ {
				if err = encoder.EncodeComplex(plaintext, values); err != nil {
					b.Error(err)
				}
			}
		})

		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/Decode", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if values = encoder.DecodeComplex(plaintext); err != nil {
					b.Error(err)
				}
			}
		})

		// Key Pair Generation
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/KeyPairGen", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				sk, pk, err = kgen.NewKeyPair()
				if err != nil {
					b.Error(err)
				}
			}
		})

		// SwitchKeyGen
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/SwitchKeyGen", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if rlk, err = kgen.NewRelinKey(sk, bdc); err != nil {
					b.Error(err)
				}
			}
		})

		// Encrypt
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/EncryptPk", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = encryptor.EncryptFromPk(plaintext, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Encrypt
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/EncryptSk", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = encryptor.EncryptFromSk(plaintext, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Decrypt
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/Decrypt", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = decryptor.Decrypt(ciphertext1, plaintext); err != nil {
					b.Error(err)
				}
			}
		})

		// Add
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/Add", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.Add(ciphertext1, ciphertext2, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Add Scalar
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/AddScalar", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.AddConst(ciphertext1, complex(3.1415, -1.4142), ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Mult Scalar
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/MultScalar", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.MultConst(ciphertext1, complex(3.1415, -1.4142), ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Mul
		receiver := ckkscontext.NewRandomCiphertext(2, levels-1, logScale)
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/Multiply", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.MulRelin(ciphertext1, ciphertext2, nil, receiver); err != nil {
					b.Error(err)
				}
			}
		})

		// Mul Relin
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/MulRelin", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.MulRelin(ciphertext1, ciphertext2, rlk, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Square Relin
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/SquareRelin", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.MulRelin(ciphertext1, ciphertext1, rlk, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Relin

		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/Relin", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.Relinearize(receiver, rlk, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Rescale
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/Rescale", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				rescale(evaluator, ciphertext1.Value()[0], receiver.Value()[0])
				rescale(evaluator, ciphertext1.Value()[1], receiver.Value()[1])
			}
		})

		// Conjugate / Rotate
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/Conjugate", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.Conjugate(ciphertext1, rotkey, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})

		// Rotate Cols
		b.Run(fmt.Sprintf("logN=%d/logQ=%d/levels=%d/decomp=%d/sigma=%.2f/RotateCols", logN, logQ, levels, bdc, sigma), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if err = evaluator.RotateColumns(ciphertext1, 1, rotkey, ciphertext1); err != nil {
					b.Error(err)
				}
			}
		})
	}
}
