-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Hyp.adj_qp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:28.536463+00:00
-- url     : https://prove2.me/submissions/e81c9f0a-ee86-4f9e-af6f-a770c9b5de15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_GlobalTheory_IndLine_Iwasawa_c_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h
namespace GlobalTheory.IndLine.Iwasawa.Hyp
theorem _root_.solution : (prY c J x y)ᵀ * J = J * (prX c J x y).map c := by
  have e : (prX c J x y).map c = -Matrix.vecMulVec (c ∘ x) (y ᵥ* J) := by
    ext i j
    have := congrFun (c_mulVec h.cc h.skew y) j
    simp only [Function.comp_apply, Pi.neg_apply] at this
    simp [prX, Matrix.vecMulVec_apply, this]
  rw [e, prY, Matrix.transpose_neg, Matrix.transpose_vecMulVec, Matrix.neg_mul, Matrix.vecMulVec_mul, Matrix.mul_neg,
    Matrix.mul_vecMulVec]
end GlobalTheory.IndLine.Iwasawa.Hyp
