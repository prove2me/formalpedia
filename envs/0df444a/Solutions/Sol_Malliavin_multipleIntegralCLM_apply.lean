-- Prove2me | solution 1 for Malliavin.multipleIntegralCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:52.009795+00:00
-- url     : https://prove2.me/submissions/50223518-0b75-4e03-bf8a-fb84fe1ce68e

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral

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
    multipleIntegralCLM hB n f = (n.factorial : ℝ) •
      iteratedIntegralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) :=
  rfl
end Malliavin
