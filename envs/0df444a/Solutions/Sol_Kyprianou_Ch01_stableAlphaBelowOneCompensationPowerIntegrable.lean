-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:27:25.044432+00:00
-- url     : https://prove2.me/submissions/251a424e-125c-41d8-8936-bf0440b9a22b

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
open MeasureTheory Real Set
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    IntegrableOn (fun r : ℝ => r ^ (-alpha))
      (Set.Ioo (0 : ℝ) 1) := by
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff (t := (1 : ℝ)) zero_lt_one).2
    (by linarith)
