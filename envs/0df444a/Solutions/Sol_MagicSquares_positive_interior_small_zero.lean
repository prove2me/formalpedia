-- Prove2me | solution 1 for MagicSquares.positive_interior_small_zero
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-21T21:28:03.457032+00:00
-- url     : https://prove2.me/submissions/d26cf632-4d5a-41f8-8c60-6ae352503d91

import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquares_positiveInteriorCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators
open MagicSquares

theorem solution (n t : Nat) (hn : 1 <= n) (htn : t < n) :
    positiveInteriorCount n t = 0 := by
  classical
  unfold positiveInteriorCount
  rw [Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [Finset.mem_filter] at hM
  obtain ⟨_, hsemi, hpos⟩ := hM
  have h0 : 0 < n := by omega
  have i0 : Fin n := ⟨0, h0⟩
  have heq : ∑ j : Fin n, ((M i0 j : Fin (t + 1)) : Nat) = t := hsemi.1 i0
  have hone : (∑ _j : Fin n, 1) = n := by simp
  have hle : (∑ _j : Fin n, 1) ≤ ∑ j : Fin n, ((M i0 j : Fin (t + 1)) : Nat) :=
    Finset.sum_le_sum (fun j _ => hpos i0 j)
  omega
