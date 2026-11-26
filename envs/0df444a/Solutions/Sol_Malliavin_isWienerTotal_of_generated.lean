-- Prove2me | solution 1 for Malliavin.isWienerTotal_of_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:34.99507+00:00
-- url     : https://prove2.me/submissions/64b4c82a-d806-477e-adee-c7170425df22

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_secondCountableTopology_randomL2_of_isWienerGenerated
import Theorems.Thm_Malliavin_isWienerTotal_of_processLpEmbedding
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_processLpEmbedding_surjective


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
    (hgen : IsWienerGenerated B) : IsWienerTotal hB := by
  let _ : SecondCountableTopology (RandomL2 P) :=
    secondCountableTopology_randomL2_of_isWienerGenerated hB hgen
  let hmeas : ∀ t, Measurable (B t) := hgen.measurable
  exact isWienerTotal_of_processLpEmbedding hB hmeas
    (processLpEmbedding_surjective P B hmeas hgen)
end Malliavin
