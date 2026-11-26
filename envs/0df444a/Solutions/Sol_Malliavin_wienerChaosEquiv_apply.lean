-- Prove2me | solution 1 for Malliavin.wienerChaosEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:25.791916+00:00
-- url     : https://prove2.me/submissions/ada9ee36-0712-4aca-abbe-b8ba803ee78e

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_wienerChaos_coordinate_eq_projection

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
theorem _root_.solution (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB)
    (F : RandomL2 P) (n : ℕ) :
    (wienerChaosEquiv hB htotal F) n =
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).orthogonalProjectionOnto F :=
  wienerChaos_coordinate_eq_projection hB
    (wienerChaos_isHilbertSum_of_total hB htotal) n F
end Malliavin
