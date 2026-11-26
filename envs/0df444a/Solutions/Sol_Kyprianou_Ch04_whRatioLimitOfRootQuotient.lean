-- Prove2me | solution 1 for Kyprianou.Ch04.whRatioLimitOfRootQuotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:29:29.884567+00:00
-- url     : https://prove2.me/submissions/55844d82-ec96-47fc-b4a3-33a6e3995e99

import Mathlib
open Filter Set MeasureTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (q r : ℕ → ℝ)
    (beta m psiBeta : ℝ)
    (hr : ∀ n, 0 < r n)
    (hpsi : psiBeta ≠ 0)
    (hq0 : Tendsto q atTop (nhds 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (nhds m)) :
    Tendsto (fun n => (q n / r n) * ((r n - beta) / (q n - psiBeta)))
      atTop (nhds (m * beta / psiBeta)) := by
  have heq (n : ℕ) :
      (q n / r n) * ((r n - beta) / (q n - psiBeta)) =
        (q n - beta * (q n / r n)) / (q n - psiBeta) := by
    rw [← mul_div_assoc, mul_sub, div_mul_cancel₀ _ (hr n).ne']
    ring
  simp_rw [heq]
  have hnum : Tendsto (fun n => q n - beta * (q n / r n))
      atTop (nhds (0 - beta * m)) :=
    hq0.sub (tendsto_const_nhds.mul hquot)
  have hden : Tendsto (fun n => q n - psiBeta)
      atTop (nhds (0 - psiBeta)) :=
    hq0.sub tendsto_const_nhds
  have hlim := hnum.div hden (by simpa using hpsi)
  have hvalue : (0 - beta * m) / (0 - psiBeta) = m * beta / psiBeta := by
    simp [mul_comm]
  rw [hvalue] at hlim
  exact hlim
