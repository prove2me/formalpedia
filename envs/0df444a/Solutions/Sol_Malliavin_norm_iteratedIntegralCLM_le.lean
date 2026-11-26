-- Prove2me | solution 1 for Malliavin.norm_iteratedIntegralCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:36.435802+00:00
-- url     : https://prove2.me/submissions/6b187c2d-6eed-4065-9f41-224859784a30

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    ‖iteratedIntegralCLM hB n f‖ ≤ ‖f‖ :=
  (iteratedIntegralFamily hB).norm_integral_le n f
end Malliavin
