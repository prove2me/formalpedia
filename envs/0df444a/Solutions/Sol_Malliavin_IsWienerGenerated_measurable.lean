-- Prove2me | solution 1 for Malliavin.IsWienerGenerated.measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:50:06.571297+00:00
-- url     : https://prove2.me/submissions/f52334aa-999e-4ffc-b3f1-7c45ddd36297

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
namespace IsWienerGenerated
theorem _root_.solution (hgen : IsWienerGenerated B) (t : ℝ≥0) :
    Measurable (B t) := by
  apply Measurable.of_comap_le
  rw [← hgen]
  exact le_iSup (fun s : ℝ≥0 ↦ MeasurableSpace.comap (B s) (borel ℝ)) t
end IsWienerGenerated
end Malliavin
