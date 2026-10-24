-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.prod_scale_log
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:28:01.910538+00:00
-- url     : https://prove2.me/submissions/29201a16-d460-466b-b99c-25cf1bbaecdf

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem solution
    {α : Type} [Fintype α] [DecidableEq α]
    (scale : α → Nat) (hscale_pos : ∀ i, 0 < scale i)
    (B : Real) (hbudget : (∑ i : α, Real.log (scale i : Real)) ≤ B) :
    0 < ∏ i : α, scale i ∧
      Real.log ((∏ i : α, scale i : Nat) : Real) ≤ B := by
  classical
  have hprod : 0 < ∏ i : α, scale i :=
    Finset.prod_pos fun i hi => hscale_pos i
  constructor
  · exact_mod_cast hprod
  · have hlog :
        Real.log ((∏ i : α, scale i : Nat) : Real) =
          ∑ i : α, Real.log (scale i : Real) := by
      simpa only [Nat.cast_prod] using
        (Real.log_prod (s := Finset.univ)
          (f := fun i : α => (scale i : Real))
          (by
            intro i hi
            exact_mod_cast (ne_of_gt (hscale_pos i))))
    rw [hlog]
    exact hbudget