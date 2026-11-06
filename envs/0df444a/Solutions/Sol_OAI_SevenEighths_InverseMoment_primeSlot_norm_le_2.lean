-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.primeSlot_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:36.935752+00:00
-- url     : https://prove2.me/submissions/fb873b80-0642-4888-9a60-2d1f3ccfca37

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

theorem solution (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by
  unfold primeSlot
  calc ‖∑ p ∈ L, if p ∈ A then a p else 0‖
      ≤ ∑ p ∈ L, ‖if p ∈ A then a p else 0‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ L, (if p ∈ A then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun p hp => by
          split_ifs with h
          · exact ha p hp
          · simp
    _ = ((L ∩ A).card : ℝ) := by
        rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
