-- Prove2me | solution 1 for GlobalTheory.MinorInt.near_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:51.202037+00:00
-- url     : https://prove2.me/submissions/86e43b71-2332-4d3e-a4c1-402b80331c51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_star_dot_self_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ G : Matrix ι ι ℂ, (∀ i j, ‖(G - 1) i j‖ < δ) →
      1 / 2 ≤ ‖G.det‖ ∧ 1 / 2 ≤ ‖(1 - (2 : ℂ) • G).det‖ ∧
        ∀ t : ι → ℂ, (∑ i, ‖t i‖ ^ 2) / 2 ≤ (star t ⬝ᵥ G *ᵥ t).re := by
  have h1 : ∀ᶠ E : ι → ι → ℂ in nhds 0, 1 / 2 < ‖(Matrix.of E + 1).det‖ := by
    have hc : Continuous fun E : ι → ι → ℂ => ‖(Matrix.of E + 1).det‖ := by
      refine Continuous.norm (Continuous.matrix_det ?_)
      exact Continuous.add continuous_id continuous_const
    refine hc.continuousAt.eventually (lt_mem_nhds ?_)
    have : Matrix.of (0 : ι → ι → ℂ) = 0 := rfl
    simp [this]; norm_num
  have h2 : ∀ᶠ E : ι → ι → ℂ in nhds 0, 1 / 2 < ‖(1 - (2 : ℂ) • (Matrix.of E + 1)).det‖ := by
    have hc : Continuous fun E : ι → ι → ℂ => ‖(1 - (2 : ℂ) • (Matrix.of E + 1)).det‖ := by
      refine Continuous.norm (Continuous.matrix_det ?_)
      have hc0 : Continuous fun E : ι → ι → ℂ => Matrix.of E + 1 :=
        Continuous.add continuous_id continuous_const
      exact continuous_const.sub (hc0.const_smul (2 : ℂ))
    refine hc.continuousAt.eventually (lt_mem_nhds ?_)
    have : Matrix.of (0 : ι → ι → ℂ) = 0 := rfl
    have h3 : (1 : Matrix ι ι ℂ) - (2 : ℂ) • (1 : Matrix ι ι ℂ) = -1 := by
      rw [two_smul]; abel
    simp only [this, zero_add, h3, det_neg]
    simp; norm_num
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨min (min (ε / 2) 1) (1 / (2 * (N + 1))), by positivity,
    (min_le_left _ _).trans (min_le_right _ _), fun G hG => ?_⟩
  have hE : dist (fun i j => (G - 1) i j) 0 < ε := by
    rw [dist_zero_right]
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    exact (hG i j).le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hGE : Matrix.of (fun i j => (G - 1) i j) + 1 = G := by
    ext i j; simp
  have h := hball hE
  rw [hGE] at h
  refine ⟨h.1.le, h.2.le, fun t => ?_⟩
  have hsplit : star t ⬝ᵥ G *ᵥ t = star t ⬝ᵥ t + star t ⬝ᵥ (G - 1) *ᵥ t := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub]; ring
  have hb : ‖star t ⬝ᵥ (G - 1) *ᵥ t‖ ≤ 1 / (2 * (N + 1)) * (∑ i, ‖t i‖) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
    have := (hG i j).le.trans (min_le_right _ _)
    calc ‖t i‖ * (‖(G - 1) i j‖ * ‖t j‖) = ‖(G - 1) i j‖ * (‖t i‖ * ‖t j‖) := by ring
      _ ≤ _ := by gcongr
  have hcs : (∑ i, ‖t i‖) ^ 2 ≤ N * ∑ i, ‖t i‖ ^ 2 := by
    simpa [hN] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖t i‖)
  have hS : 0 ≤ ∑ i, ‖t i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb2 : 1 / (2 * (N + 1)) * (∑ i, ‖t i‖) ^ 2 ≤ (∑ i, ‖t i‖ ^ 2) / 2 := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hre := (Complex.abs_re_le_norm (star t ⬝ᵥ (G - 1) *ᵥ t))
  rw [hsplit, Complex.add_re, star_dot_self_re]
  have := neg_abs_le (star t ⬝ᵥ (G - 1) *ᵥ t).re
  linarith
end GlobalTheory.MinorInt
