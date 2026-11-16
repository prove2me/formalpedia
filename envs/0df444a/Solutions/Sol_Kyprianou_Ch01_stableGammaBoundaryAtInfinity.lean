-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaBoundaryAtInfinity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:38:52.627163+00:00
-- url     : https://prove2.me/submissions/d421c2dd-f359-4f77-a8af-9a39f3866041

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open Real Filter
set_option autoImplicit false
theorem solution
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    Filter.Tendsto
      (fun x : ℝ => (Real.exp (-(u * x)) - 1) * (x ^ (-alpha) / (-alpha)))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hlin : Tendsto (fun x : ℝ => u * x) atTop atTop :=
    Tendsto.const_mul_atTop hu tendsto_id
  have h1 : Tendsto (fun x : ℝ => Real.exp (-(u * x)) - 1) atTop (nhds (0 - 1)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).sub_const 1
  have h2 : Tendsto (fun x : ℝ => x ^ (-alpha) / (-alpha)) atTop (nhds (0 / (-alpha))) :=
    (tendsto_rpow_neg_atTop ha0).div_const _
  simpa using h1.mul h2
