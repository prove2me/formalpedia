-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanAffineCoefficientsNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:54:18.468797+00:00
-- url     : https://prove2.me/submissions/deffcfd1-754c-4ae4-8059-e642e5c323e2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

/-- The affine-support discount intercept and exponential slope are nonnegative. -/
theorem solution
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    let u := min y b
    0 ≤ K - (1 + 1 / phi) * Real.exp u ∧
      0 ≤ Real.exp u / phi := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  let u : ℝ := min y b
  change 0 ≤ K - (1 + 1 / phi) * Real.exp u ∧
    0 ≤ Real.exp u / phi
  have hp : 0 < 1 + phi := by linarith
  have hlog : 0 < K * phi / (1 + phi) :=
    div_pos (mul_pos hK hphi) hp
  have heb : Real.exp b = K * phi / (1 + phi) :=
    Real.exp_log hlog
  have heub : Real.exp u ≤ K * phi / (1 + phi) := by
    calc
      Real.exp u ≤ Real.exp b :=
        Real.exp_le_exp.mpr (min_le_right y b)
      _ = K * phi / (1 + phi) := heb
  have hfactor : 0 ≤ 1 + 1 / phi := by positivity
  have heq : (1 + 1 / phi) * (K * phi / (1 + phi)) = K := by
    field_simp [ne_of_gt hphi, ne_of_gt hp]
    ring
  constructor
  · have hm := mul_le_mul_of_nonneg_left heub hfactor
    rw [heq] at hm
    linarith
  · positivity
