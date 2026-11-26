-- Prove2me | solution 1 for Malliavin.inner_iteratedIntegralCLM_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:00.123477+00:00
-- url     : https://prove2.me/submissions/19592e57-c318-4318-a4db-c07accd700f0

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
theorem _root_.solution (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (iteratedIntegralCLM hB m f) (iteratedIntegralCLM hB n g) = 0 :=
  (iteratedIntegralFamily hB).differentOrder hmn f g
end Malliavin
