-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.eq_on_common_core
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:25:39.783818+00:00
-- url     : https://prove2.me/submissions/15a16d0d-ed47-43b0-b27b-47402d7cd0b4

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

theorem aux_eocc_swap_mem {n : ℕ} (R : Finset (Fin n)) (i j : Fin n) (hi : i ∈ R) (hj : j ∈ R)
    (x : Fin n) (hx : x ∈ R) : Equiv.swap i j x ∈ R := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

theorem aux_eocc_subset_iff {n : ℕ} (R T : Finset (Fin n)) (i j : Fin n) (hi : i ∈ R)
    (hj : j ∈ R) :
    R ⊆ T.map (Equiv.swap i j).symm.toEmbedding ↔ R ⊆ T := by
  constructor
  · intro h x hx
    have h1 := h (aux_eocc_swap_mem R i j hi hj x hx)
    rw [Finset.mem_map_equiv] at h1
    simpa using h1
  · intro h x hx
    rw [Finset.mem_map_equiv]
    simpa using h (aux_eocc_swap_mem R i j hi hj x hx)

theorem aux_eocc_perm_eq {n : ℕ} (v : Game n) (c : Finset (Fin n) → ℝ)
    (hv : ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S)
    (i j : Fin n) (hij : ∀ R : Finset (Fin n), R.Nonempty → c R ≠ 0 → i ∈ R ∧ j ∈ R) :
    permGame (Equiv.swap i j) v = v := by
  apply Subtype.ext
  funext T
  show v.1 (T.map (Equiv.swap i j).symm.toEmbedding) = v.1 T
  rw [hv, hv]
  apply Finset.sum_congr rfl
  intro R hR
  have hRne : R.Nonempty := (Finset.mem_filter.mp hR).2
  by_cases hc : c R = 0
  · simp [hc]
  · obtain ⟨hi, hj⟩ := hij R hRne hc
    unfold unanimity
    rw [if_congr (aux_eocc_subset_iff R T i j hi hj) rfl rfl]

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ) (hS : IsSymmetric φ)
    (v : Game n) (c : Finset (Fin n) → ℝ)
    (hv : ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S)
    (i j : Fin n) (hij : ∀ R : Finset (Fin n), R.Nonempty → c R ≠ 0 → i ∈ R ∧ j ∈ R) :
    φ v i = φ v j := by
  have h := hS (Equiv.swap i j) v i
  rw [aux_eocc_perm_eq v c hv i j hij, Equiv.swap_apply_left] at h
  exact h.symm
