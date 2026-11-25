-- Prove2me | solution 1 for Kyprianou.Ch04.positiveRootTendsToZeroOfPositiveQuotientLimitV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:39:03.440319+00:00
-- url     : https://prove2.me/submissions/88019487-5c26-426b-ac55-296b2f569e32

import Mathlib.Topology.Filter
import Mathlib.Topology.Instances.Real.Lemmas
open Filter
open scoped Topology
set_option autoImplicit false

/-- Positive root vanishes if the positive discount/root ratio has a positive limit. -/
theorem solution
    (q r : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hr : ∀ n, 0 < r n)
    (m : ℝ) (hm : 0 < m)
    (hq0 : Tendsto q atTop (𝓝 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (𝓝 m)) :
    Tendsto r atTop (𝓝 0) := by
  have hdiv := hq0.div hquot (ne_of_gt hm)
  have hfunc : (q / (fun n : ℕ => q n / r n)) = r := by
    funext n
    change q n / (q n / r n) = r n
    field_simp [ne_of_gt (hq n), ne_of_gt (hr n)]
  simpa [hfunc] using hdiv
