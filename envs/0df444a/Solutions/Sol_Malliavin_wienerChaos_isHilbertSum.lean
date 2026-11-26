-- Prove2me | solution 1 for Malliavin.wienerChaos_isHilbertSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:58.696226+00:00
-- url     : https://prove2.me/submissions/549ae0fc-aefc-4a1a-aa1e-560927e27040

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
    IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ) :=
  wienerChaos_isHilbertSum_of_total hB (isWienerTotal_of_generated hB hgen)
end Malliavin
