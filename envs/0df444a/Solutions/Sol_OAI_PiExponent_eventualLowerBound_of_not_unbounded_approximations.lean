-- Prove2me | solution 1 for OAI.PiExponent.eventualLowerBound_of_not_unbounded_approximations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:04:38.687659+00:00
-- url     : https://prove2.me/submissions/29eeffa7-5be1-4afc-af9c-ec56600bd928

import Mathlib.Tactic.Push
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions


namespace OAI

namespace PiExponent

 













end PiExponent

end OAI

open OAI.PiExponent in
theorem solution {x : ℝ}
    (h : ∀ ν : ℝ, 2 < ν →
      ¬ ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ), Q ≤ q ∧
        |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) :
    EventualLowerBound x := by
  intro ν hν
  have hbad := h ν hν
  push Not at hbad
  obtain ⟨Q, hQ⟩ := hbad
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  intro p q hq
  exact (hQ p q ((le_max_left Q 2).trans hq)).le
