-- Prove2me | solution 1 for IncrKnapsack.PTAS.representation_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:29:36.894995+00:00
-- url     : https://prove2.me/submissions/af43dba7-29b0-4b13-aa2a-f7739bdc3a47

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

open IncrKnapsack.PTAS in
theorem solution (I : Instance) (p : Fin I.n → ℝ) (S : Sol I) :
    Psi I p S = contrib I p S := by
  unfold Psi contrib Sol.set
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold psiItem
  cases h : S i with
  | none => simp
  | some s =>
    simp only [Option.some.injEq, exists_eq_left']
    unfold lamPlus
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> ring
