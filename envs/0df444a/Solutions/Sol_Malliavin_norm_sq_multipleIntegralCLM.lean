-- Prove2me | solution 1 for Malliavin.norm_sq_multipleIntegralCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:43.208986+00:00
-- url     : https://prove2.me/submissions/6b1f4c9d-54fc-4733-989a-ac25a0df911e

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
    (f : IteratedKernel n) :
    ‖multipleIntegralCLM hB n f‖ ^ 2 = (n.factorial : ℝ) *
      ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_multipleIntegralCLM hB n f f
end Malliavin
