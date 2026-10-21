-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.log_linear_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:10:24.577114+00:00
-- url     : https://prove2.me/submissions/17793b5b-ee67-4e4c-97e5-f25c250b2fec

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution (n : Nat) (hn : n ≤ 1) :
    PowerSeries.coeff n (PowerSeries.log ℂ) = if n = 0 then 0 else 1 := by
  cases n with
  | zero => simp
  | succ n =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      simp