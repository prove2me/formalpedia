-- Prove2me | solution 1 for GeneralCK.Certificates.PilotData.log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T20:57:33.180108+00:00
-- url     : https://prove2.me/submissions/82ccec99-f883-4ab0-be01-887a92b4a730

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_LogBounds
import Theorems.Thm_GeneralCK_Certificates_checkLog_sound

open GeneralCK.Certificates

theorem solution :
    (34657359 / 50000000) ≤ Real.log (2 / 1) ∧
    Real.log (2 / 1) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
