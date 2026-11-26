-- Prove2me | solution 1 for Kyprianou.Ch04.positiveRootTendsToZeroOfPositiveQuotientLimit
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:20.279617+00:00
-- url     : https://prove2.me/submissions/7927119e-b7ef-4677-8b53-a78cab734e06

import Mathlib
open Filter
set_option autoImplicit false
theorem _root_.solution
    (q r : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hr : ∀ n, 0 < r n)
    (m : ℝ) (hm : 0 < m)
    (hq0 : Tendsto q atTop (nhds 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (nhds m)) :
    Tendsto r atTop (nhds 0) := by
  have h : Tendsto (fun n => q n / (q n / r n)) atTop (nhds (0 / m)) := hq0.div hquot hm.ne'
  rw [zero_div] at h
  refine h.congr fun n => ?_
  have h1 := (hq n).ne'
  have h2 := (hr n).ne'
  field_simp

