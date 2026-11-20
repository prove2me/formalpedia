-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneScaleSkewSignIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:56:20.303015+00:00
-- url     : https://prove2.me/submissions/db272e29-86e5-4060-9603-e1b2611e3edb

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (cpos cneg xi : ℝ) (hsum : 0 < cpos + cneg) :
    let c : ℝ := Real.pi * (cpos + cneg) / 2
    let beta : ℝ := (cpos - cneg) / (cpos + cneg)
    let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0
    c * |xi| * beta * (2 / Real.pi) * sgn = (cpos - cneg) * xi := by
  intro c beta sgn
  have hsign : |xi| * sgn = xi := by
    dsimp [sgn]
    by_cases hx : 0 < xi
    · simp [hx, abs_of_pos hx]
    · by_cases hn : xi < 0
      · simp [hx, hn, abs_of_neg hn]
      · have hz : xi = 0 := by linarith
        subst xi
        simp
  have hcoeff :
      c * beta * (2 / Real.pi) = cpos - cneg := by
    dsimp [c, beta]
    field_simp [ne_of_gt hsum, Real.pi_ne_zero]
  calc
    c * |xi| * beta * (2 / Real.pi) * sgn =
        (c * beta * (2 / Real.pi)) * (|xi| * sgn) := by ring
    _ = (cpos - cneg) * xi := by rw [hcoeff, hsign]
