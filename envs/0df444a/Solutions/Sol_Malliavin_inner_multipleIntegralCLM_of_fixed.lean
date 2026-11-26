-- Prove2me | solution 1 for Malliavin.inner_multipleIntegralCLM_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:37.603724+00:00
-- url     : https://prove2.me/submissions/97687930-7f9e-41e3-975c-065e8c183c64

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_inner_multipleIntegralCLM
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
    (f g : IteratedKernel n)
    (hf : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f = f)
    (hg : symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g = g) :
    inner ℝ (multipleIntegralCLM hB n f) (multipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ f g := by
  simpa only [hf, hg] using inner_multipleIntegralCLM hB n f g
end Malliavin
