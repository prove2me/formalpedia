-- Prove2me | solution 1 for Malliavin.norm_sq_eq_tsum_starProjection_wienerChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:28.174182+00:00
-- url     : https://prove2.me/submissions/f3f525e1-5482-4d4b-8dae-1768985173bf

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_wienerChaos_coordinate_eq_projection
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



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
    ‖F‖ ^ 2 = ∑' n : ℕ,
      ‖(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (hsum.linearIsometryEquiv F)
  rw [hsum.linearIsometryEquiv.norm_map] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [show (∑' n : ℕ, ‖hsum.linearIsometryEquiv F n‖ ^ 2) =
      ∑' n : ℕ,
      ‖(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F‖ ^ 2 by
    congr 1
    funext n
    rw [wienerChaos_coordinate_eq_projection hB hsum n F]
    rfl] at h
  exact h
end Malliavin
