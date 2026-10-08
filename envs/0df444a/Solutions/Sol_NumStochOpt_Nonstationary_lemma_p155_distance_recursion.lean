-- Prove2me | solution 1 for NumStochOpt.Nonstationary.lemma_p155_distance_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:51:36.328304+00:00
-- url     : https://prove2.me/submissions/80ec85e1-26d9-4559-b4e6-0bfa8b872e24

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

open scoped RealInnerProductSpace

set_option autoImplicit false

namespace C6615783Aux

open NumStochOpt.QuasiFejer

theorem projX_spec {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXclosed : IsClosed X)
    (hXconv : Convex ℝ X) (hne : X.Nonempty) (y : EuclideanSpace ℝ (Fin n)) :
    projX X y ∈ X ∧ ∀ z ∈ X, ‖y - projX X y‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
  obtain ⟨v, hv, hveq⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hXclosed.isComplete hXconv y
  have hex : ∃ x ∈ X, ∀ z ∈ X, ‖y - x‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    refine ⟨v, hv, fun z hz => ?_⟩
    have : ‖y - v‖ ≤ ‖y - z‖ := by
      rw [hveq]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨z, hz⟩ : X)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  unfold projX
  rw [dif_pos hex]
  exact hex.choose_spec

theorem projX_nonexp {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXclosed : IsClosed X)
    (hXconv : Convex ℝ X) (y z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ X) :
    ‖projX X y - z‖ ≤ ‖y - z‖ := by
  obtain ⟨hp, hmin⟩ := projX_spec X hXclosed hXconv ⟨z, hz⟩ y
  set p := projX X y
  have hinf : ‖y - p‖ = ⨅ w : X, ‖y - w‖ := by
    haveI : Nonempty X := ⟨⟨z, hz⟩⟩
    apply le_antisymm
    · apply le_ciInf
      intro w
      have h := hmin w w.2
      nlinarith [norm_nonneg (y - p), norm_nonneg (y - (w : EuclideanSpace ℝ (Fin n)))]
    · exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨p, hp⟩ : X)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hXconv hp).1 hinf z hz
  have h1 : y - z = (y - p) + (p - z) := by abel
  have h2 : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 + 2 * ⟪y - p, p - z⟫ + ‖p - z‖ ^ 2 := by
    rw [h1]; exact norm_add_sq_real _ _
  have h3 : ⟪y - p, p - z⟫ = -⟪y - p, z - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  have h4 : ‖p - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by nlinarith [sq_nonneg ‖y - p‖]
  nlinarith [norm_nonneg (p - z), norm_nonneg (y - z)]

end C6615783Aux

open NumStochOpt.QuasiFejer RealInnerProductSpace in
theorem solution {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hXclosed : IsClosed X) (hXconv : Convex ℝ X)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (s : ℕ)
    (hrec : x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ NumStochOpt.QuasiFejer.optimalSet f X)
    (hnear : ‖xstar - x s‖ = Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X)) :
    Metric.infDist (x (s + 1)) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 ≤
      Metric.infDist (x s) (NumStochOpt.QuasiFejer.optimalSet f X) ^ 2 + 2 * ρ s * ⟪g s, xstar - x s⟫
        + ρ s ^ 2 * ‖g s‖ ^ 2 := by
  have hxX : xstar ∈ X := hxstar.1
  have hy := C6615783Aux.projX_nonexp X hXclosed hXconv (x s - ρ s • g s) xstar hxX
  rw [← hrec] at hy
  have hd : Metric.infDist (x (s + 1)) (optimalSet f X) ≤ ‖x (s + 1) - xstar‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hxstar
  have h0 : 0 ≤ Metric.infDist (x (s + 1)) (optimalSet f X) := Metric.infDist_nonneg
  have hsq : Metric.infDist (x (s + 1)) (optimalSet f X) ^ 2 ≤ ‖x s - ρ s • g s - xstar‖ ^ 2 :=
    pow_le_pow_left₀ h0 (hd.trans hy) 2
  have hexp : ‖x s - ρ s • g s - xstar‖ ^ 2
      = ‖xstar - x s‖ ^ 2 + 2 * ρ s * ⟪g s, xstar - x s⟫ + ρ s ^ 2 * ‖g s‖ ^ 2 := by
    have e : x s - ρ s • g s - xstar = -(xstar - x s) - ρ s • g s := by abel
    rw [e, norm_sub_sq_real, norm_neg, inner_neg_left, real_inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm (g s) (xstar - x s)]
    ring
  rw [hnear] at hexp
  linarith
