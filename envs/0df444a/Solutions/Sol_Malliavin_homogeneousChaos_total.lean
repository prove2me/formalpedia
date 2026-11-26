-- Prove2me | solution 1 for Malliavin.homogeneousChaos_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:55.825041+00:00
-- url     : https://prove2.me/submissions/e4c48c3a-e5bc-42af-8123-96ca7c992325

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_isWienerTotal_of_generated

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (hgen : IsWienerGenerated B) :
    (⨆ n : ℕ, (homogeneousChaos hB n : Submodule ℝ (RandomL2 P))).topologicalClosure = ⊤ :=
  isWienerTotal_of_generated hB hgen
end Malliavin
