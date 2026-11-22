-- Prove2me | solution 1 for MasulloRH.mission_riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-11-21T21:40:22.29969+00:00
-- url     : https://prove2.me/submissions/ff8accf9-2743-486c-a8e0-0e5f9761270d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_zero_free_right
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-- Masullo mission root: critical-strip RH from the source-specific nonvanishing child. -/
theorem solution :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s hs0 hs1 hz
  by_contra hne
  rcases lt_or_gt_of_ne hne with hleft | hright
  · have hs_neg : ∀ n : ℕ, s ≠ -(n : ℂ) := by
      intro n heq
      have heq_re := congrArg Complex.re heq
      simp only [Complex.neg_re, Complex.natCast_re] at heq_re
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hs_one : s ≠ 1 := by
      intro heq
      have heq_re := congrArg Complex.re heq
      simp only [Complex.one_re] at heq_re
      linarith
    have hreflect : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_one_sub hs_neg hs_one, hz]
      simp
    have hright' : (1 / 2 : ℝ) < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hone' : 1 - s ≠ 1 := by
      intro heq
      have heq_re := congrArg Complex.re heq
      simp only [Complex.sub_re, Complex.one_re] at heq_re
      linarith
    exact MasulloRH.zero_free_right (1 - s) hright' hone' hreflect
  · have hs_one : s ≠ 1 := by
      intro heq
      have heq_re := congrArg Complex.re heq
      simp only [Complex.one_re] at heq_re
      linarith
    exact MasulloRH.zero_free_right s hright hs_one hz
