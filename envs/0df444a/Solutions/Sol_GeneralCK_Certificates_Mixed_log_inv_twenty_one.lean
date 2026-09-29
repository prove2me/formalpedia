-- Prove2me | solution 1 for GeneralCK.Certificates.Mixed.log_inv_twenty_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:12:56.65049+00:00
-- url     : https://prove2.me/submissions/a82ca689-0ebd-4270-aa04-41fa6115c680

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_LogBounds
import Theorems.Thm_GeneralCK_Certificates_checkLog_sound
import Theorems.Thm_GeneralCK_Certificates_PilotData_log_two

namespace GeneralCK.Certificates.Mixed





theorem log_scaled (s : ℝ) (k : ℕ) (hs : 0 < s) :
    Real.log ((2 : ℝ)^k*s) = (k : ℝ)*Real.log 2 + Real.log s := by
  rw [Real.log_mul (by positivity) (ne_of_gt hs), Real.log_pow]

theorem log_inv_eq (q : ℝ) : Real.log (1/q) = -Real.log q := by simp [one_div]





end GeneralCK.Certificates.Mixed

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.Mixed
theorem solution : (608904487 / 200000000) ≤ -Real.log (1 / 21) ∧
    -Real.log (1 / 21) ≤ (76113061 / 25000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(21 / 16) = 1/(1 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]
