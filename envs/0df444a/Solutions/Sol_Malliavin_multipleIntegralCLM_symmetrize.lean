-- Prove2me | solution 1 for Malliavin.multipleIntegralCLM_symmetrize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:17.157709+00:00
-- url     : https://prove2.me/submissions/d17e1d8e-ae93-4593-ade0-5135596ddd69

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_symmetrizeL_symmetrizeL
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
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) =
      multipleIntegralCLM hB n f := by
  simp only [multipleIntegralCLM, smul_apply,
    ContinuousLinearMap.comp_apply, symmetrizeL_symmetrizeL]
end Malliavin
