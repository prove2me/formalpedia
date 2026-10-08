-- Prove2me | solution 1 for NumStochOpt.Nonstationary.lemma_p156_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:01:16.749266+00:00
-- url     : https://prove2.me/submissions/90d09276-4229-4bb2-be7e-c9e63363d6d1

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

namespace P077e1ad5

open NumStochOpt.QuasiFejer

theorem projX_spec {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcpt : IsCompact X)
    (hne : X.Nonempty) (y : EuclideanSpace ℝ (Fin n)) :
    projX X y ∈ X ∧ ∀ z ∈ X, ‖y - projX X y‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
  have hex : ∃ x ∈ X, ∀ z ∈ X, ‖y - x‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    obtain ⟨x, hx, hmin⟩ := hXcpt.exists_isMinOn hne
      ((continuous_const.sub continuous_id).norm.pow 2).continuousOn
    exact ⟨x, hx, fun z hz => hmin hz⟩
  unfold projX
  rw [dif_pos hex]
  exact hex.choose_spec

theorem projX_le {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X)
    (hXcpt : IsCompact X) (y z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ X) :
    projX X y ∈ X ∧ ‖projX X y - z‖ ≤ ‖y - z‖ := by
  obtain ⟨hp, hmin⟩ := projX_spec X hXcpt ⟨z, hz⟩ y
  set p := projX X y
  refine ⟨hp, ?_⟩
  have hinf : ‖y - p‖ = ⨅ w : X, ‖y - w‖ := by
    have : Nonempty X := ⟨⟨z, hz⟩⟩
    apply le_antisymm
    · apply le_ciInf
      intro w
      have := hmin w w.2
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    · exact ciInf_le (f := fun w : X => ‖y - (w : EuclideanSpace ℝ (Fin n))‖)
        ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩ ⟨p, hp⟩
  have hang := (norm_eq_iInf_iff_real_inner_le_zero hXconv hp).1 hinf z hz
  have key : ‖p - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    have e : y - z = (y - p) + (p - z) := by abel
    rw [e, norm_add_sq_real]
    have : inner ℝ (y - p) (p - z) = - inner ℝ (y - p) (z - p) := by
      rw [← inner_neg_right, neg_sub]
    nlinarith [norm_nonneg (y - p)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key

end P077e1ad5

theorem solution {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X) (hXcpt : IsCompact X)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hbound : ∀ s, ‖g s‖ ≤ C)
    (a b : ℕ) (hab : a ≤ b) (hxa : x a ∈ X) :
    ‖x b - x a‖ ≤ ∑ s ∈ Finset.Ico a b, ‖x (s + 1) - x s‖ ∧
      ∑ s ∈ Finset.Ico a b, ‖x (s + 1) - x s‖ ≤ C * ∑ s ∈ Finset.Ico a b, ρ s := by
  have hmem : ∀ s, a ≤ s → x s ∈ X := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact hxa
    | succ k _ ih =>
      rw [hrec k]
      exact (P077e1ad5.projX_le X hXconv hXcpt _ _ ih).1
  constructor
  · have h := dist_le_Ico_sum_dist x hab
    rw [dist_comm] at h
    simp only [dist_eq_norm] at h
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun s _ => ?_
    exact norm_sub_rev _ _
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsa : a ≤ s := (Finset.mem_Ico.1 hs).1
    have h := (P077e1ad5.projX_le X hXconv hXcpt (x s - ρ s • g s) (x s) (hmem s hsa)).2
    rw [← hrec s] at h
    have e : x s - ρ s • g s - x s = -(ρ s • g s) := by abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg (hρnn s)] at h
    calc ‖x (s + 1) - x s‖ ≤ ρ s * ‖g s‖ := h
      _ ≤ ρ s * C := mul_le_mul_of_nonneg_left (hbound s) (hρnn s)
      _ = C * ρ s := mul_comm _ _
