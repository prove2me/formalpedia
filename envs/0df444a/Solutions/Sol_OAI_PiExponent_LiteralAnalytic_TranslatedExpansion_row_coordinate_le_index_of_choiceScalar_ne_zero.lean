-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.row_coordinate_le_index_of_choiceScalar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:42:17.05543+00:00
-- url     : https://prove2.me/submissions/8fe16702-db27-4ab3-9e00-cab0bbfa7259

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : ChoiceFamily d H) (r : Row d H)
    (hr : choiceScalar d r (f r) ≠ 0) :
    ∀ i : Fin d.m, r.2.1 i.succ ≤ (f r).1.1 i := by
  intro i
  by_contra h
  have hlt : (f r).1.1 i < r.2.1 i.succ := Nat.lt_of_not_ge h
  have hprod :
      (∏ j : Fin d.m,
        ((f r).1.1 j).choose (r.2.1 j.succ) *
          (((f r).1.1 j - r.2.1 j.succ)).choose ((f r).2.1 j) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hlt]
  simp [choiceScalar, hprod] at hr