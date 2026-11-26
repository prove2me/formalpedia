-- Prove2me | solution 1 for Malliavin.hasSum_starProjection_wienerChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:26.196538+00:00
-- url     : https://prove2.me/submissions/df8852d5-8eaf-459e-87b6-7e34a9c44990

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
theorem _root_.solution
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (F : RandomL2 P) :
    HasSum (fun n : ℕ =>
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F) F := by
  have h := hsum.hasSum_linearIsometryEquiv_symm (hsum.linearIsometryEquiv F)
  rw [hsum.linearIsometryEquiv.symm_apply_apply] at h
  convert h using 1
  funext n
  rw [wienerChaos_coordinate_eq_projection hB hsum n F]
  rfl
end Malliavin
