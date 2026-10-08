-- Prove2me | solution 1 for NumStochOpt.Nonstationary.lemma_p155_conditions_1_2a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:20:31.787972+00:00
-- url     : https://prove2.me/submissions/aab4629c-a3d7-44f5-afb0-6438e33070ae

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

open Filter Topology

namespace P90554122

lemma projX_spec {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXcpt : IsCompact X)
    (hXne : X.Nonempty) (y : EuclideanSpace ℝ (Fin n)) :
    NumStochOpt.QuasiFejer.projX X y ∈ X ∧
      ∀ z ∈ X, ‖y - NumStochOpt.QuasiFejer.projX X y‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
  have hex : ∃ x ∈ X, ∀ z ∈ X, ‖y - x‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    obtain ⟨x, hx, hmin⟩ := hXcpt.exists_isMinOn hXne
      (f := fun z => ‖y - z‖ ^ 2) (by fun_prop)
    exact ⟨x, hx, fun z hz => hmin hz⟩
  have : NumStochOpt.QuasiFejer.projX X y = hex.choose := by
    unfold NumStochOpt.QuasiFejer.projX
    simp only [dif_pos hex]
  rw [this]
  exact hex.choose_spec

end P90554122

open Filter Topology in
theorem solution {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X) (hXcpt : IsCompact X)
    (hXne : X.Nonempty)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hρ0 : Tendsto ρ atTop (𝓝 0)) (hbound : ∀ s, ‖g s‖ ≤ C) :
    (∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ ∀ s, x s ∈ K) ∧
      Tendsto (fun s => ‖x (s + 1) - x s‖) atTop (𝓝 0) := by
  have hmem : ∀ s, x (s + 1) ∈ X := fun s => by
    rw [hrec s]; exact (P90554122.projX_spec X hXcpt hXne _).1
  refine ⟨⟨insert (x 0) X, hXcpt.insert _, fun s => ?_⟩, ?_⟩
  · cases s with
    | zero => exact Set.mem_insert _ _
    | succ k => exact Set.mem_insert_of_mem _ (hmem k)
  · have hlim : Tendsto (fun s => 2 * (ρ s * C)) atTop (𝓝 0) := by
      have := (hρ0.mul_const C).const_mul 2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun s => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 1] with s hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    have hxs : x (k + 1) ∈ X := hmem k
    set y := x (k + 1) - ρ (k + 1) • g (k + 1) with hy
    obtain ⟨_, hmin⟩ := P90554122.projX_spec X hXcpt hXne y
    have h1 : ‖y - NumStochOpt.QuasiFejer.projX X y‖ ≤ ‖y - x (k + 1)‖ := by
      have := hmin _ hxs
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    have h2 : ‖y - x (k + 1)‖ ≤ ρ (k + 1) * C := by
      rw [hy, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (hρnn _)]
      exact mul_le_mul_of_nonneg_left (hbound _) (hρnn _)
    rw [hrec (k + 1)]
    calc ‖NumStochOpt.QuasiFejer.projX X y - x (k + 1)‖
        ≤ ‖NumStochOpt.QuasiFejer.projX X y - y‖ + ‖y - x (k + 1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖y - NumStochOpt.QuasiFejer.projX X y‖ + ‖y - x (k + 1)‖ := by rw [norm_sub_rev]
      _ ≤ 2 * (ρ (k + 1) * C) := by linarith
