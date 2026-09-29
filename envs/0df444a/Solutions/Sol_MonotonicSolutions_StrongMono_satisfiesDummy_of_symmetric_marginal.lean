-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.satisfiesDummy_of_symmetric_marginal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:49:03.267511+00:00
-- url     : https://prove2.me/submissions/e2a4f5e6-4c19-4f3d-848c-82f32d62945e

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- The zero game. -/
def aux_sdsm_zero (n : ℕ) : Game n := ⟨fun _ => 0, rfl⟩

theorem aux_sdsm_perm_zero {n : ℕ} (π : Equiv.Perm (Fin n)) :
    permGame π (aux_sdsm_zero n) = aux_sdsm_zero n := rfl

theorem aux_sdsm_zero_const {n : ℕ} (φ : Game n → Fin n → ℝ) (hS : IsSymmetric φ)
    (i j : Fin n) : φ (aux_sdsm_zero n) j = φ (aux_sdsm_zero n) i := by
  have h := hS (Equiv.swap i j) (aux_sdsm_zero n) i
  rw [aux_sdsm_perm_zero, Equiv.swap_apply_left] at h
  exact h

theorem aux_sdsm_zero_val {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hA : IsAllocationProcedure φ) (hS : IsSymmetric φ) (i : Fin n) :
    φ (aux_sdsm_zero n) i = 0 := by
  have h := hA (aux_sdsm_zero n)
  have hc : ∀ j, φ (aux_sdsm_zero n) j = φ (aux_sdsm_zero n) i :=
    fun j => aux_sdsm_zero_const φ hS i j
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this.ne'
  have h0 : (aux_sdsm_zero n).1 Finset.univ = 0 := rfl
  rw [h0] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hn
  · exact h1

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hA : IsAllocationProcedure φ) (hS : IsSymmetric φ) (hM : IsMarginal φ) :
    SatisfiesDummy φ := by
  intro v i hv
  have h := hM v (aux_sdsm_zero n) i (fun S => by
    rw [hv S]
    simp [marginal, aux_sdsm_zero])
  rw [h]
  exact aux_sdsm_zero_val φ hA hS i
