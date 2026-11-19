-- Prove2me | solution 1 for LevyStochCalc.Probability.charlierScaled_forward_diff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:59:54.387056+00:00
-- url     : https://prove2.me/submissions/ff562f4b-c879-4312-821a-7b4bc17d128e

import Definitions.Def_LevyStochCalc_Probability_Charlier_F000

open LevyStochCalc.Probability

theorem solution (s : ℕ) (lam x : ℝ) :
    charlierScaled (s + 1) lam (x + 1) - charlierScaled (s + 1) lam x
      = ((s : ℝ) + 1) * charlierScaled s lam x := by
  induction s generalizing x with
  | zero =>
    simp only [Nat.cast_zero, zero_add, one_mul, charlierScaled_one, charlierScaled_zero]
    ring
  | succ s ih =>
    rw [charlierScaled_succ (s + 1) lam (x + 1), charlierScaled_succ (s + 1) lam x]
    have h1 : x + 1 - 1 = x := by ring
    rw [h1]
    have ih1 := ih (x - 1)
    have h2 : x - 1 + 1 = x := by ring
    rw [h2] at ih1
    have ih2 := ih x
    have hsucc : charlierScaled (s + 1) lam x =
        x * charlierScaled s lam (x - 1) - lam * charlierScaled s lam x :=
      charlierScaled_succ s lam x
    have hA : charlierScaled (s + 1) lam (x - 1) =
        charlierScaled (s + 1) lam x - ((s : ℝ) + 1) * charlierScaled s lam (x - 1) := by
      linarith
    have hB : charlierScaled (s + 1) lam (x + 1) =
        charlierScaled (s + 1) lam x + ((s : ℝ) + 1) * charlierScaled s lam x := by
      linarith
    rw [hA, hB]
    push_cast
    calc (x + 1) * charlierScaled (s + 1) lam x -
          lam * (charlierScaled (s + 1) lam x + ((s : ℝ) + 1) * charlierScaled s lam x) -
          (x * (charlierScaled (s + 1) lam x - ((s : ℝ) + 1) * charlierScaled s lam (x - 1)) -
            lam * charlierScaled (s + 1) lam x)
        = charlierScaled (s + 1) lam x +
            ((s : ℝ) + 1) * (x * charlierScaled s lam (x - 1) - lam * charlierScaled s lam x) := by
          ring
      _ = charlierScaled (s + 1) lam x + ((s : ℝ) + 1) * charlierScaled (s + 1) lam x := by
          rw [← hsucc]
      _ = ((s : ℝ) + 1 + 1) * charlierScaled (s + 1) lam x := by ring
