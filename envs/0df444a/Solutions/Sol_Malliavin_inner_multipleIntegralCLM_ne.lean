-- Prove2me | solution 1 for Malliavin.inner_multipleIntegralCLM_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:46.349798+00:00
-- url     : https://prove2.me/submissions/dc01bce1-4287-4d9e-bcaf-efb7be7951f2

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_multipleIntegralCLM_apply
import Theorems.Thm_Malliavin_inner_iteratedIntegralCLM_ne


set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (multipleIntegralCLM hB m f) (multipleIntegralCLM hB n g) = 0 := by
  rw [multipleIntegralCLM_apply, multipleIntegralCLM_apply, real_inner_smul_left,
    real_inner_smul_right, inner_iteratedIntegralCLM_ne hB hmn, mul_zero, mul_zero]
end Malliavin
