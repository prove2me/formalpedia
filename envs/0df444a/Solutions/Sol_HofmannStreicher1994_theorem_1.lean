-- Prove2me | solution 1 for HofmannStreicher1994.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T23:25:13.411895+00:00
-- url     : https://prove2.me/submissions/c399cbad-ca01-4af9-8e7c-b8e97717b473

import Theorems.Thm_HofmannStreicher1994_uip_underivable

/-!
Reduction of the literal existential theorem to the open explicit-witness goal.
This file imports an unproved draft, so it does not establish the independence
theorem. Its purpose is to make the packaging implication explicit and checkable.
-/

open HofmannStreicher1994

theorem solution :
    ∃ A, TypeWf [] A ∧
      ¬ ∃ t, TermWf (diagonalContext A) t (diagonalConclusion A) := by
  exact ⟨counterexampleType, uip_underivable.1, uip_underivable.2.1⟩
