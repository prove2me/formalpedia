-- Prove2me | solution 1 for OAI.PiExponent.pi_floor_bracket_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-12T19:40:00.295823+00:00
-- url     : https://prove2.me/submissions/f7dea037-894f-42b8-a8f2-dcb406f96698
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound

 theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤
          |Real.pi - ((Int.floor ((q : ℝ) * Real.pi) : ℤ) : ℝ) / (q : ℝ)| ∧
        (q : ℝ) ^ (-nu) ≤
          |Real.pi - (((Int.floor ((q : ℝ) * Real.pi) + 1 : ℤ) : ℝ) / (q : ℝ))| := by
  obtain ⟨Q, hQ, h⟩ := OAI.PiExponent.rational_approximation_lower_bound nu hnu
  refine ⟨Q, hQ, ?_⟩
  intro q hq
  exact ⟨h (Int.floor ((q : ℝ) * Real.pi)) q hq,
    h (Int.floor ((q : ℝ) * Real.pi) + 1) q hq⟩
