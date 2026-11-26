-- Prove2me | solution 1 for Malliavin.norm_multipleIntegralCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:46.035038+00:00
-- url     : https://prove2.me/submissions/22fa5814-ee9a-4588-b3f1-701d4e0c9543

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_norm_multipleIntegralCLM
import Theorems.Thm_Malliavin_norm_symmetrizeL_apply_le


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ ≤ Real.sqrt (n.factorial : ℝ) * ‖f‖ := by
  rw [norm_multipleIntegralCLM]
  exact mul_le_mul_of_nonneg_left
    (norm_symmetrizeL_apply_le (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2 f)
    (Real.sqrt_nonneg _)
end Malliavin
