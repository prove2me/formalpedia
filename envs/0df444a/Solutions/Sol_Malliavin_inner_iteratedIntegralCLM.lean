-- Prove2me | solution 1 for Malliavin.inner_iteratedIntegralCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:44.950776+00:00
-- url     : https://prove2.me/submissions/882b2de8-ded0-4f2c-99dd-aa44e58aeee2

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
    (f g : IteratedKernel n) :
    inner ℝ (iteratedIntegralCLM hB n f) (iteratedIntegralCLM hB n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n :=
  (iteratedIntegralFamily hB).sameOrder n f g
end Malliavin
