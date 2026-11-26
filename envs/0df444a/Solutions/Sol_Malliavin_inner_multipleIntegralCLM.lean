-- Prove2me | solution 1 for Malliavin.inner_multipleIntegralCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:50.338804+00:00
-- url     : https://prove2.me/submissions/67a525b7-1633-442a-8366-b4fef4b8fe74

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_integral_inner_symmetrizeL_eq_factorial_smul_setIntegral
import Theorems.Thm_Malliavin_inner_iteratedIntegralCLM
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel n) :
    inner ℝ (multipleIntegralCLM hB n f) (multipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g) := by
  rw [multipleIntegralCLM]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_left,
    real_inner_smul_right]
  rw [inner_iteratedIntegralCLM, MeasureTheory.L2.inner_def]
  have htile := integral_inner_symmetrizeL_eq_factorial_smul_setIntegral n f g
  rw [← Nat.cast_smul_eq_nsmul ℝ] at htile
  rw [htile]
  simp only [smul_eq_mul]
end Malliavin
