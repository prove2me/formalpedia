-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.det_mul_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:27.454979+00:00
-- url     : https://prove2.me/submissions/c7e7d4e0-72c2-4298-b62d-ce0a0eb62d04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
import Theorems.Thm_GlobalTheory_SgGlob_Iota_adjugate_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution {T : E} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {x y : Fin (r + 1) → E}
    (h : TF r T *ᵥ y + Z *ᵥ x = 0) :
    Z.det * x (Fin.last r) = T * lead Z r (Nat.le_succ r) * y (Fin.last r) := by
  have e := congrFun (congrArg (Z.adjugate *ᵥ ·) h) (Fin.last r)
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  have e2 : ((Z.adjugate * TF r T) *ᵥ y) (Fin.last r) =
      -(T * lead Z r (Nat.le_succ r) * y (Fin.last r)) := by
    simp [TF, Matrix.mulVec, dotProduct, Matrix.mul_diagonal, adjugate_last, mul_comm]
  linear_combination e - e2
end GlobalTheory.SgGlob.Iota
