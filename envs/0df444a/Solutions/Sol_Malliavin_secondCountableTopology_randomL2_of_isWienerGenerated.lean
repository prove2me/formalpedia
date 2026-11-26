-- Prove2me | solution 1 for Malliavin.secondCountableTopology_randomL2_of_isWienerGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:10:06.959912+00:00
-- url     : https://prove2.me/submissions/adcb11d6-099b-4d8d-b7d5-1c48e96b1a2c

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_isSeparable_of_isWienerGenerated

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
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    SecondCountableTopology (RandomL2 P) := by
  let _ : @MeasureTheory.IsSeparable Ω mΩ P :=
    isSeparable_of_isWienerGenerated hB hgen
  let _ : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact @MeasureTheory.Lp.SecondCountableTopology Ω ℝ mΩ inferInstance P 2
    inferInstance inferInstance inferInstance inferInstance
end Malliavin
