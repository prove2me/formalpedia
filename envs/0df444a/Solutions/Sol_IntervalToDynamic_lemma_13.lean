-- Prove2me | solution 1 for IntervalToDynamic.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T16:31:22.84659+00:00
-- url     : https://prove2.me/submissions/4eee52d6-f177-41f6-9d49-204de54e0463

import Mathlib
import Definitions.Def_IntervalToDynamic_proj
import Definitions.Def_IntervalToDynamic_correctedGrad

namespace Aux_IntervalToDynamic_lemma_13

lemma obtuse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (hXv : Convex ℝ X) {y p u : E}
    (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection X y p) (hu : u ∈ X) :
    0 ≤ inner ℝ (y - p) (p - u) := by
  haveI : Nonempty X := ⟨⟨u, hu⟩⟩
  have key : ‖y - p‖ = ⨅ w : X, ‖y - (w : E)‖ := by
    apply le_antisymm
    · refine le_ciInf (fun w => ?_)
      have h1 := hp.2 w w.2
      rw [dist_eq_norm, dist_eq_norm] at h1
      exact h1
    · have hbdd : BddBelow (Set.range fun w : X => ‖y - (w : E)‖) := by
        refine ⟨(0 : ℝ), ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg _
      exact ciInf_le hbdd ⟨p, hp.1⟩
  have h := (norm_eq_iInf_iff_real_inner_le_zero hXv hp.1).mp key u hu
  have : p - u = -(u - p) := by abel
  rw [this, inner_neg_right]
  linarith

lemma case0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g y p u : E) (hn : y - p = 0) :
    inner ℝ g (p - u) ≤ inner ℝ g (y - u) := by
  have hsplit : y - u = (y - p) + (p - u) := by abel
  rw [hsplit, hn, zero_add]

lemma case1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g y p u : E) (hn : y - p ≠ 0) (hnp : 0 ≤ inner ℝ (y - p) (p - u)) :
    ‖g + (max (-(inner ℝ g (y - p))) 0 / ‖y - p‖ ^ 2) • (y - p)‖ ≤ ‖g‖ ∧
      inner ℝ g (p - u) ≤
        inner ℝ (g + (max (-(inner ℝ g (y - p))) 0 / ‖y - p‖ ^ 2) • (y - p)) (y - u) := by
  have hsplit : y - u = (y - p) + (p - u) := by abel
  rw [hsplit]
  generalize y - p = n at hn hnp ⊢
  generalize p - u = q at hnp ⊢
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
  by_cases hgn : 0 ≤ inner ℝ g n
  · have hm : max (-(inner ℝ g n)) 0 = 0 := max_eq_right (by linarith)
    rw [hm, zero_div, zero_smul, add_zero]
    refine ⟨le_rfl, ?_⟩
    rw [inner_add_right]
    linarith
  · push_neg at hgn
    have hm : max (-(inner ℝ g n)) 0 = -(inner ℝ g n) := max_eq_left (by linarith)
    rw [hm]
    obtain ⟨c, hcdef⟩ : ∃ c, c = -(inner ℝ g n) / ‖n‖ ^ 2 := ⟨_, rfl⟩
    rw [← hcdef]
    have hc0 : 0 ≤ c := by rw [hcdef]; exact div_nonneg (by linarith) (by positivity)
    have hc : c * ‖n‖ ^ 2 = -(inner ℝ g n) := by
      rw [hcdef]; field_simp
    refine ⟨?_, ?_⟩
    · have hsq : ‖g + c • n‖ ^ 2 ≤ ‖g‖ ^ 2 := by
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hc0, mul_pow]
        nlinarith [mul_nonneg hc0 (show 0 ≤ -(inner ℝ g n) by linarith)]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    · rw [inner_add_right, inner_add_left, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
      nlinarith [mul_nonneg hc0 hnp]

end Aux_IntervalToDynamic_lemma_13

open IntervalToDynamic Aux_IntervalToDynamic_lemma_13 in
theorem solution {d : ℕ} (hd : 0 < d) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXv : Convex ℝ X)
    (g : EuclideanSpace ℝ (Fin d)) (G : ℝ) (hG : 0 ≤ G) (hg : ‖g‖ ≤ G) (u y : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X) :
    ‖correctedGrad g (y - proj X y)‖ ≤ ‖g‖ ∧ ‖g‖ ≤ G ∧
      inner ℝ g (proj X y - u) ≤ inner ℝ (correctedGrad g (y - proj X y)) (y - u) := by
  have hex : ∃ p, OnlineConvexOpt.FirstOrder.IsMetricProjection X y p := by
    obtain ⟨p, hp, hdist⟩ := hXc.exists_infDist_eq_dist ⟨u, hu⟩ y
    refine ⟨p, hp, fun z hz => ?_⟩
    rw [← hdist]
    exact Metric.infDist_le_dist_of_mem hz
  have hp : OnlineConvexOpt.FirstOrder.IsMetricProjection X y (proj X y) :=
    Classical.epsilon_spec hex
  have hnp := obtuse hXv hp hu
  unfold correctedGrad
  by_cases hn : y - proj X y = 0
  · rw [if_pos hn]
    exact ⟨le_rfl, hg, case0 g y (proj X y) u hn⟩
  · rw [if_neg hn]
    obtain ⟨h1, h2⟩ := case1 g y (proj X y) u hn hnp
    exact ⟨h1, hg, h2⟩
