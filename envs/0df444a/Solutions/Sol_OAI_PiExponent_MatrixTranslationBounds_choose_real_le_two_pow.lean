-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.choose_real_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:16:53.38799+00:00
-- url     : https://prove2.me/submissions/d1bb1ee6-f0a5-4a21-a35b-25b1ea88ace0

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators

theorem solution (k m : ℕ) :
    (Nat.choose k m : ℝ) ≤ (2 : ℝ) ^ k := by
  exact_mod_cast Nat.choose_le_two_pow k m