-- Prove2me | solution 1 for Malliavin.integral_iteratedIntegralCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:46.699507+00:00
-- url     : https://prove2.me/submissions/15c716ab-cb82-47fb-bf4c-eaddbc01b945

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
theorem _root_.solution (hB : IsPreBrownianReal B P) {n : ℕ} (hn : 0 < n)
    (f : IteratedKernel n) :
    ∫ ω, iteratedIntegralCLM hB n f ω ∂P = 0 :=
  (iteratedIntegralFamily hB).centered n hn f
end Malliavin
