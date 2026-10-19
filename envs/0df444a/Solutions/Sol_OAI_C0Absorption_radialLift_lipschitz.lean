-- Prove2me | solution 1 for OAI.C0Absorption.radialLift_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:22:19.422216+00:00
-- url     : https://prove2.me/submissions/90c21db9-954d-4b53-a7c5-1c353ebbb4ca

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open Set Filter Topology
open scoped NNReal BigOperators
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators
variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
theorem h41_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) :
    ‖x‖ * dist (NormedSpace.normalize x) (NormedSpace.normalize y) ≤ 2 * dist x y := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    rw [NormedSpace.normalize_zero_eq_zero, dist_zero_right, NormedSpace.norm_normalize hx, dist_zero_right]
    have := norm_nonneg x
    linarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [dist_eq_norm, dist_eq_norm]
  have key : ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) = (x - y) + (1 - ‖x‖ / ‖y‖) • y := by
    rw [smul_sub, NormedSpace.norm_smul_normalize]
    simp only [NormedSpace.normalize, smul_smul]
    rw [sub_smul, one_smul, div_eq_mul_inv]
    abel
  have h1 : ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ = ‖(x - y) + (1 - ‖x‖ / ‖y‖) • y‖ := by
    rw [← key, norm_smul, Real.norm_of_nonneg hxn.le]
  rw [h1]
  have h2 : ‖(1 - ‖x‖ / ‖y‖) • y‖ = |‖y‖ - ‖x‖| := by
    rw [norm_smul, Real.norm_eq_abs]
    have : (1 - ‖x‖ / ‖y‖) * ‖y‖ = ‖y‖ - ‖x‖ := by field_simp
    rw [← abs_of_pos hyn, ← abs_mul, abs_of_pos hyn, this]
  have h3 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y
  calc ‖(x - y) + (1 - ‖x‖ / ‖y‖) • y‖ ≤ ‖x - y‖ + ‖(1 - ‖x‖ / ‖y‖) • y‖ := norm_add_le _ _
    _ ≤ 2 * ‖x - y‖ := by rw [h2]; linarith

theorem solution (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) : LipschitzWith 3 (radialLift ζ) := by
  have hb : ∀ b : Metric.closedBall (0 : E) 1, ‖ζ b‖ ≤ 1 := by
    intro b
    have h1 := hζ.dist_le_mul b zeroBall
    rw [h0, dist_zero_right] at h1
    have h2 : dist b zeroBall ≤ 1 := by
      rw [Subtype.dist_eq]
      have hb2 := b.2
      rw [Metric.mem_closedBall] at hb2
      exact hb2
    simp only [NNReal.coe_one, one_mul] at h1
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [radialLift, dist_eq_norm]
  have e : ‖x‖ • ζ (normalizedBall x) - ‖y‖ • ζ (normalizedBall y)
      = ‖x‖ • (ζ (normalizedBall x) - ζ (normalizedBall y)) + (‖x‖ - ‖y‖) • ζ (normalizedBall y) := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  have h1 : ‖ζ (normalizedBall x) - ζ (normalizedBall y)‖ ≤ dist (NormedSpace.normalize x) (NormedSpace.normalize y) := by
    rw [← dist_eq_norm]
    have := hζ.dist_le_mul (normalizedBall x) (normalizedBall y)
    simpa [Subtype.dist_eq, normalizedBall] using this
  have h2 := h41_norm_bound x y
  rw [dist_eq_norm x y] at h2
  have h3 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h4 := hb (normalizedBall y)
  calc ‖‖x‖ • (ζ (normalizedBall x) - ζ (normalizedBall y)) + (‖x‖ - ‖y‖) • ζ (normalizedBall y)‖
      ≤ ‖‖x‖ • (ζ (normalizedBall x) - ζ (normalizedBall y))‖ + ‖(‖x‖ - ‖y‖) • ζ (normalizedBall y)‖ :=
        norm_add_le _ _
    _ = ‖x‖ * ‖ζ (normalizedBall x) - ζ (normalizedBall y)‖ + |‖x‖ - ‖y‖| * ‖ζ (normalizedBall y)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg x), Real.norm_eq_abs]
    _ ≤ ‖x‖ * dist (NormedSpace.normalize x) (NormedSpace.normalize y) + ‖x - y‖ * 1 := by
        gcongr
    _ ≤ ((3 : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; linarith

