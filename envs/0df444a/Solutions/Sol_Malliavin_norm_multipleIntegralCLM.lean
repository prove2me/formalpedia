-- Prove2me | solution 1 for Malliavin.norm_multipleIntegralCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:29.503439+00:00
-- url     : https://prove2.me/submissions/daf299e1-4a63-43e9-9302-54b4dc0828a9

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_norm_sq_multipleIntegralCLM
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
    ‖multipleIntegralCLM hB n f‖ = Real.sqrt (n.factorial : ℝ) *
      ‖symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f‖ := by
  have h := congrArg Real.sqrt (norm_sq_multipleIntegralCLM hB n f)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] using h
end Malliavin
