-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanAffineSupportTouchesValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:54:29.560549+00:00
-- url     : https://prove2.me/submissions/fbb98cbb-921c-4172-871e-600eae802533

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

/-- The clipped-barrier affine support equals the explicit McKean value at y. -/
theorem solution
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    let u := min y b
    mckeanValue K b phi y =
      (K - (1 + 1 / phi) * Real.exp u) +
        (Real.exp u / phi) * Real.exp (-phi * (y - u)) := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  let u : ℝ := min y b
  change mckeanValue K b phi y =
    (K - (1 + 1 / phi) * Real.exp u) +
      (Real.exp u / phi) * Real.exp (-phi * (y - u))
  by_cases hy : y < b
  · have hu : u = y := min_eq_left hy.le
    change (if y < b then K - Real.exp y else
      (K - Real.exp b) * Real.exp (-phi * (y - b))) =
        (K - (1 + 1 / phi) * Real.exp u) +
          (Real.exp u / phi) * Real.exp (-phi * (y - u))
    rw [if_pos hy, hu]
    simp
    ring
  · have hu : u = b := min_eq_right (le_of_not_gt hy)
    have hp : 0 < 1 + phi := by linarith
    have hlog : 0 < K * phi / (1 + phi) :=
      div_pos (mul_pos hK hphi) hp
    have heb : Real.exp b = K * phi / (1 + phi) :=
      Real.exp_log hlog
    have hA : K - (1 + 1 / phi) * Real.exp b = 0 := by
      rw [heb]
      field_simp [ne_of_gt hphi, ne_of_gt hp]
      ring
    have hB : Real.exp b / phi = K - Real.exp b := by
      rw [heb]
      field_simp [ne_of_gt hphi, ne_of_gt hp]
      ring
    change (if y < b then K - Real.exp y else
      (K - Real.exp b) * Real.exp (-phi * (y - b))) =
        (K - (1 + 1 / phi) * Real.exp u) +
          (Real.exp u / phi) * Real.exp (-phi * (y - u))
    rw [if_neg hy, hu, hA, hB]
    ring
