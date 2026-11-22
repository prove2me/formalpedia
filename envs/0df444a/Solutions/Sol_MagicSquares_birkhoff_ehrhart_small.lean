-- Prove2me | solution 1 for MagicSquares.birkhoff_ehrhart_small
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-22T10:10:11.231233+00:00
-- url     : https://prove2.me/submissions/70622aed-1a14-44d2-8a2d-cc793dbba9de

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
import Theorems.Thm_MagicSquares_semi_magic_vanishing

set_option autoImplicit false
set_option maxHeartbeats 0

open MagicSquares
open scoped BigOperators

theorem solution (n : Nat) (hn : 1 <= n) (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount n t : Rat)) : forall t : Nat, 1 <= t -> t < n -> p.eval (-(t : Rat)) = (-1 : Rat) ^ ((n - 1) ^ 2) * ((Set.ncard {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)}) : Rat) := by
  intro t ht1 htn
  have hLHS : p.eval (-((t : Nat) : Rat)) = 0 := by
    have h1 : (1 : Int) ≤ (((t : Nat)) : Int) := by exact_mod_cast ht1
    have h2 : (((t : Nat)) : Int) ≤ ((((n : Nat)) : Int)) - 1 := by omega
    have h := semi_magic_vanishing n hn p hp (((t : Nat)) : Int) h1 h2
    simpa using h
  have h0 : Set.ncard {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)} = 0 := by
    have hempty : {M : Matrix (Fin n) (Fin n) Rat | (exists D, D ∈ doublyStochastic Rat (Fin n) ∧ M = (t : Rat) • D) ∧ forall i j, 0 < M i j ∧ exists k : Nat, M i j = (k : Rat)} = ∅ := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨D, hD, hND⟩, hpos⟩
      obtain ⟨i0⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      have hNrow0 : ∑ j, N i0 j = (t : Rat) := by
        have e1 : ∑ j, N i0 j = ∑ j, (t : Rat) * D i0 j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hND, Matrix.smul_apply, smul_eq_mul]
        rw [e1, ← Finset.mul_sum, sum_row_of_mem_doublyStochastic hD i0, mul_one]
      have hbound1 : ∀ j, ∃ k : Nat, N i0 j = (k : Rat) ∧ 1 ≤ k := by
        intro j
        obtain ⟨k, hk⟩ := (hpos i0 j).2
        have h0 : (0 : Rat) < N i0 j := (hpos i0 j).1
        rw [hk] at h0
        have hkp : 0 < k := by exact_mod_cast h0
        refine ⟨k, hk, ?_⟩
        omega
      choose k hk using hbound1
      have h1n : (∑ _k ∈ (Finset.univ : Finset (Fin n)), (1 : Nat)) = n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
      have hksum : n ≤ ∑ j, k j := by
        have hle : (∑ _k ∈ (Finset.univ : Finset (Fin n)), (1 : Nat)) ≤ ∑ j, k j :=
          Finset.sum_le_sum (fun j _ => (hk j).2)
        rw [h1n] at hle
        exact hle
      have htk : ∑ j, k j = t := by
        have e1 : (∑ j, ((k j : Nat) : Rat)) = ∑ j, N i0 j :=
          Finset.sum_congr rfl (fun j _ => ((hk j).1).symm)
        have hcast : (((∑ j, k j : Nat)) : Rat) = (((t : Nat)) : Rat) := by
          push_cast
          rw [e1]
          exact hNrow0
        exact Nat.cast_injective hcast
      omega
    rw [hempty, Set.ncard_empty]
  rw [hLHS, h0, Nat.cast_zero, mul_zero]
