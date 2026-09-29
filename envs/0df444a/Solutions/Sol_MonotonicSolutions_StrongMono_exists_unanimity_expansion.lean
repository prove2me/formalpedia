-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.exists_unanimity_expansion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:49:31.611631+00:00
-- url     : https://prove2.me/submissions/d3f5b047-41e8-4b8a-be0c-d039ecad098c

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- The zeta transform on coalitions: `c ↦ (S ↦ ∑_{R ⊆ S} c R)`. -/
noncomputable def aux_ue_zeta (n : ℕ) :
    (Finset (Fin n) → ℝ) →ₗ[ℝ] (Finset (Fin n) → ℝ) where
  toFun c S := ∑ R ∈ S.powerset, c R
  map_add' c d := by
    funext S
    simp [Finset.sum_add_distrib]
  map_smul' a c := by
    funext S
    simp [Finset.mul_sum]

theorem aux_ue_zeta_apply (n : ℕ) (c : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    aux_ue_zeta n c S = ∑ R ∈ S.powerset, c R := rfl

theorem aux_ue_zeta_injective (n : ℕ) : Function.Injective (aux_ue_zeta n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  funext S
  induction S using Finset.strongInduction with
  | H S ih =>
    have h0 : aux_ue_zeta n c S = 0 := by rw [hc]; rfl
    rw [aux_ue_zeta_apply, ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self S)] at h0
    have h1 : ∑ R ∈ S.powerset.erase S, c R = 0 := by
      apply Finset.sum_eq_zero
      intro R hR
      rw [Finset.mem_erase, Finset.mem_powerset] at hR
      exact ih R (Finset.ssubset_iff_subset_ne.mpr ⟨hR.2, hR.1⟩)
    rw [h1, add_zero] at h0
    simpa using h0

theorem aux_ue_zeta_surjective (n : ℕ) : Function.Surjective (aux_ue_zeta n) :=
  LinearMap.injective_iff_surjective.mp (aux_ue_zeta_injective n)

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (v : Game n) :
    ∃ c : Finset (Fin n) → ℝ, ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S := by
  obtain ⟨c, hc⟩ := aux_ue_zeta_surjective n v.1
  have hS : ∀ S, v.1 S = ∑ R ∈ S.powerset, c R := fun S => by
    rw [← hc]; rfl
  have hc0 : c ∅ = 0 := by
    have := hS ∅
    rw [v.2] at this
    simpa using this.symm
  refine ⟨c, fun S => ?_⟩
  rw [hS S, Finset.sum_filter]
  have e : ∀ R ∈ (Finset.univ : Finset (Fin n)).powerset,
      (if R.Nonempty then c R * unanimity R S else 0) = if R ⊆ S then c R else 0 := by
    intro R _
    unfold unanimity
    rcases R.eq_empty_or_nonempty with h | h
    · subst h; simp [hc0]
    · simp [h]
  rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext R; simp
  · intros; rfl
