-- Prove2me | solution 1 for MasulloAudit.log_translation_bound_fails_near_identity
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:25:51.348336+00:00
-- url     : https://prove2.me/submissions/1a0bca8d-23f3-48d3-95b3-2cc89dca0029

import Mathlib

open Filter
open scoped Topology

theorem solution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (U : ℝ → H →L[ℂ] H) (u : H) (hu : u ≠ 0) (hzero : U 0 u = u)
    (hcont : ContinuousAt (fun t => U t u) 0) (a b s C : ℝ) (hs : 0 < s) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      C * max (Real.exp (a*t)) (Real.exp (b*t)) * |t| ^ (s/2) < ‖U t‖ := by
  let f := fun t : ℝ => C * max (Real.exp (a*t)) (Real.exp (b*t)) * |t| ^ (s/2) * ‖u‖
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous f := by
      dsimp [f]
      fun_prop (disch := positivity)
    have hval : f 0 = 0 := by simp [f, Real.zero_rpow (ne_of_gt (half_pos hs))]
    have ht : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := hc.continuousAt.continuousWithinAt
    rwa [hval] at ht
  have horbit : Tendsto (fun t => ‖U t u‖) (𝓝[>] 0) (𝓝 ‖u‖) := by
    have ht : Tendsto (fun t => ‖U t u‖) (𝓝[>] 0) (𝓝 ‖U 0 u‖) :=
      hcont.norm.continuousWithinAt
    rwa [hzero] at ht
  obtain ⟨d, hd, hdu⟩ := exists_between (norm_pos_iff.mpr hu)
  filter_upwards [hlim.eventually_lt_const hd, horbit.eventually_const_lt hdu] with t ht ht'
  have ht := ht.trans ht'
  exact lt_of_mul_lt_mul_right (lt_of_lt_of_le ht ((U t).le_opNorm u)) (norm_nonneg u)
