-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_combined_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:39:02.887655+00:00
-- url     : https://prove2.me/submissions/91d5cf24-69f4-4e1c-b355-5357eaadf30f

import Mathlib
set_option autoImplicit false

/-- Combine the separate complementary jump and grid errors. -/
theorem solution (ja jb jc ga gb gc a Q J : ℝ)
    (hj : |ja-jb-jc| ≤ a*J) (hg : |ga-gb-gc| ≤ a*Q) :
    |(ja-jb-(ga-gb))-(jc-gc)| ≤ a*(Q+J) := by
  rw [show ja-jb-(ga-gb)-(jc-gc) = (ja-jb-jc)-(ga-gb-gc) by ring]
  exact (abs_sub _ _).trans (by linarith)
