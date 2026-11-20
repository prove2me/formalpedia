-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftIBPAtInfinity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:30:51.914657+00:00
-- url     : https://prove2.me/submissions/6ff1aa29-3969-48d9-8d02-2715251a4b8b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    Tendsto
      (fun r : ℝ => (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
  have hexp :
      Tendsto (fun r : ℝ => Complex.exp (w * (r : ℂ)))
        Filter.atTop (nhds (0 : ℂ)) := by
    simpa [Complex.tendsto_exp_nhds_zero_iff] using
      tendsto_const_nhds.neg_mul_atTop hwre tendsto_id
  have hp : Tendsto (fun r : ℝ => r ^ (-alpha))
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_rpow_neg_atTop h0
  have hpdiv : Tendsto (fun r : ℝ => r ^ (-alpha) / (-alpha))
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hp.div_const (-alpha)
  have hcast : Tendsto
      (fun r : ℝ => (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hpdiv
  simpa only [sub_zero, zero_sub, mul_zero] using
    (hexp.sub_const (1 : ℂ)).mul hcast
