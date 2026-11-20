-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftMellinRhsHolomorphic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T13:11:06.685811+00:00
-- url     : https://prove2.me/submissions/b13da58f-dde3-4f45-8059-c6286e60b104

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
set_option autoImplicit false

theorem solution (alpha : ℝ) :
    AnalyticOnNhd ℂ
      (fun w : ℂ =>
        ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
          Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)))
      {w : ℂ | w.re < 0} := by
  intro w hw
  change w.re < 0 at hw
  have hslit : -w ∈ Complex.slitPlane := by
    exact Or.inl (by simpa using (neg_pos.mpr hw))
  have hlog : AnalyticAt ℂ (fun z : ℂ => Complex.log (-z)) w :=
    (analyticAt_id.neg).clog hslit
  have hexp : AnalyticAt ℂ
      (fun z : ℂ =>
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-z))) w :=
    (analyticAt_const.mul hlog).cexp
  exact analyticAt_const.mul hexp
