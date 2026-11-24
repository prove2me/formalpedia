-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.LhsSum.one_le_abs_prod_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:00:42.984377+00:00
-- url     : https://prove2.me/submissions/b69e3532-5680-452f-bab6-f1fb17d5a02a

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_prod_realEmb_eq_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR.LhsSum
theorem _root_.solution [IsTotallyReal F] (y : 𝓞 F) (hy : y ≠ 0) :
    1 ≤ |∏ τ : F →+* ℝ, τ (y : F)| := by
  rw [prod_realEmb_eq_norm, ← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs h
  have h2 : (((Algebra.norm ℤ y : ℤ) : ℚ) : ℝ) = ((Algebra.norm ℤ y : ℤ) : ℝ) := by push_cast; rfl
  rw [h2]
  exact_mod_cast h1
end GlobalTheory.LipschitzTR.LhsSum
