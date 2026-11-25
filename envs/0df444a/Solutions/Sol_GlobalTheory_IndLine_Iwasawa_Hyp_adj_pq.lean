-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Hyp.adj_pq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:52.329566+00:00
-- url     : https://prove2.me/submissions/2c3ae176-89ec-4dce-a1d5-330ba13b9eef

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
theorem _root_.solution : (prX c J x y)ᵀ * J = J * (prY c J x y).map c := by
  have e : (prY c J x y).map c = Matrix.vecMulVec (c ∘ y) (x ᵥ* J) := by
    ext i j
    have := congrFun (c_mulVec h.cc h.skew x) j
    simp only [Function.comp_apply, Pi.neg_apply] at this
    simp [prY, Matrix.vecMulVec_apply, this]
  rw [e, prX, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec]
end GlobalTheory.IndLine.Iwasawa.Hyp
