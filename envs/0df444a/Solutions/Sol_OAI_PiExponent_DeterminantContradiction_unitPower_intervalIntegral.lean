-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitPower_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:33:49.008046+00:00
-- url     : https://prove2.me/submissions/fa44dff9-34a3-4268-b2b4-d85d8823fb49

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ∫ t in (0 : ℝ)..1, (1 - t) ^ n = 1 / (n + 1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ n) (d := 1)]
  norm_num
