-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finsum_positive_negative_balance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:24:32.306916+00:00
-- url     : https://prove2.me/submissions/3e33f736-7d8b-4b8e-b3ab-e881b2ee09d6

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution
    {ι : Type} (v : ι → Int)
    (hfinite : (Function.support v).Finite)
    (hsum : (∑ᶠ i : ι, (v i : Real)) = 0) :
    (∑ᶠ i : ι, max 0 (v i : Real)) =
      (∑ᶠ i : ι, max 0 (-(v i : Real))) := by
  have h1 : (Function.support fun i => max 0 (v i : Real)).Finite := by
    apply hfinite.subset
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    intro h; apply hi; simp [h]
  have h2 : (Function.support fun i => max 0 (-(v i : Real))).Finite := by
    apply hfinite.subset
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    intro h; apply hi; simp [h]
  have key : (∑ᶠ i : ι, (v i : Real)) =
      (∑ᶠ i : ι, max 0 (v i : Real)) - (∑ᶠ i : ι, max 0 (-(v i : Real))) := by
    rw [← finsum_sub_distrib h1 h2]
    congr 1; funext i
    rcases le_total 0 (v i : Real) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  linarith
