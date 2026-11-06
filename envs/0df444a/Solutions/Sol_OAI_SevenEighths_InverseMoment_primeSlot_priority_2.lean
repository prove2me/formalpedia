-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.primeSlot_priority
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:35.11413+00:00
-- url     : https://prove2.me/submissions/fe5caa10-cfbb-4811-82f7-a359043682bd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem solution (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (A ∪ B) = primeSlot L a A + primeSlot L a (B \ A) := by
  unfold primeSlot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;> simp [hA, hB]
