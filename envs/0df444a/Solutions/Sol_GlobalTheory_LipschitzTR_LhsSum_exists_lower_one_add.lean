-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.LhsSum.exists_lower_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:07.452724+00:00
-- url     : https://prove2.me/submissions/fd8c5ef9-f349-4b38-8321-2ef3aef3bf73

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
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
theorem _root_.solution (w : ℂ) (hw : w.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖w + (t : ℂ)‖ := by
  have him : 0 < |w.im| := abs_pos.2 hw
  refine ⟨|w.im| / (|w.im| + 1 + ‖w‖), by positivity, fun t => ?_⟩
  have h1 : |w.im| ≤ ‖w + (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w + (t : ℂ))
    simpa using this
  have h2 : |t| ≤ ‖w + (t : ℂ)‖ + ‖w‖ := by
    have := norm_sub_le (w + (t : ℂ)) w
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hn : 0 ≤ ‖w‖ := norm_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
end GlobalTheory.LipschitzTR.LhsSum
