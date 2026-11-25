-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteTruncationJumpDifferenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:45:22.997321+00:00
-- url     : https://prove2.me/submissions/7b3211c0-fa93-476d-9d49-8d1c35a311fa

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} [DecidableEq I]
    (τ : I → ℝ) (hτ : Function.Injective τ) (j : I → ℝ)
    (a d : ℝ) (S : Finset I) (s : I) :
    (a+d*τ s+∑ i ∈ S, if τ i ≤ τ s then j i else 0) -
      (a+d*τ s+∑ i ∈ S, if τ i < τ s then j i else 0) =
        if s ∈ S then j s else 0 := by
  have hterm (i : I) :
      (if τ i ≤ τ s then j i else 0) - (if τ i < τ s then j i else 0) =
        if i = s then j i else 0 := by
    by_cases he : i = s
    · subst i
      simp
    · by_cases hlt : τ i < τ s
      · simp [he,hlt,hlt.le]
      · have hn : ¬ τ i ≤ τ s := fun hle => hlt (lt_of_le_of_ne hle (fun e => he (hτ e)))
        simp [he,hlt,hn]
  calc
    _ = ∑ i ∈ S, ((if τ i ≤ τ s then j i else 0) -
        (if τ i < τ s then j i else 0)) := by
          rw [Finset.sum_sub_distrib]
          ring
    _ = ∑ i ∈ S, if i = s then j i else 0 := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := Finset.sum_ite_eq' S s j
