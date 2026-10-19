-- Prove2me | solution 3 for OAI.PiExponent.pi_floor_bracket_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T13:52:34.075051+00:00
-- url     : https://prove2.me/submissions/047f396b-d077-4134-b92d-0c4323405c9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤
          |Real.pi - ((Int.floor ((q : ℝ) * Real.pi) : ℤ) : ℝ) / (q : ℝ)| ∧
        (q : ℝ) ^ (-nu) ≤
          |Real.pi - (((Int.floor ((q : ℝ) * Real.pi) + 1 : ℤ) : ℝ) / (q : ℝ))| := by
  obtain ⟨Q, hQ, hbound⟩ :=
    OAI.PiExponent.rational_approximation_lower_bound nu hnu
  refine ⟨Q, hQ, ?_⟩
  intro q hq
  constructor
  · exact hbound (Int.floor ((q : ℝ) * Real.pi)) q hq
  · exact hbound (Int.floor ((q : ℝ) * Real.pi) + 1) q hq
