-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.LhsSum.summable_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:10.001779+00:00
-- url     : https://prove2.me/submissions/4f71aee7-be80-4360-8901-ba8b3652d649

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_wt_nonneg
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR.LhsSum
theorem _root_.solution : Summable wt := by
  have hA : Summable (fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ))) := Real.summable_abs_int_rpow (by norm_num)
  have hB : Summable (fun m : ℤ => if m = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le wt_nonneg (fun m => ?_) (hA.add hB)
  by_cases hm : m = 0
  · subst hm
    simp [wt, Real.zero_rpow]
  · simp only [hm, if_false, add_zero]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    rw [Real.rpow_neg (abs_nonneg _), wt]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    apply inv_anti₀ (by positivity)
    nlinarith [abs_nonneg (m : ℝ)]
end GlobalTheory.LipschitzTR.LhsSum
