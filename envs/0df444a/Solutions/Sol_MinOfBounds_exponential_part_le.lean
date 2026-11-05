-- Prove2me | solution 1 for MinOfBounds.exponential_part_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:59.420336+00:00
-- url     : https://prove2.me/submissions/fe5878a0-7b40-48fb-8ea7-f8b297d03e7b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_MinOfBounds_Arith
import Theorems.Thm_MinOfBounds_min_time_le
import Theorems.Thm_MinOfBounds_factor_goes_into_exponent
import Theorems.Thm_VariableBound_Paper_timeCor_eq
import Theorems.Thm_VariableBound_Paper_two_le_expM
import Theorems.Thm_VariableBound_Paper_two_le_expN


set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution (C₁ C₂ q : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    q * (2 ^ q * min (timeM C₁ k m) (timeN C₂ k n) ^ q) ≤ timeCor (q * max C₁ C₂ + q) k m n := by
  rw [timeCor_eq]
  unfold timeMin
  refine Nat.le_floor ?_
  have h := factor_goes_into_exponent q (max C₁ C₂) _ (le_min (two_le_expM hk hm) (two_le_expN hk hn)) (min_time_le C₁ C₂ hk hm hn)
  have e : ((q * max C₁ C₂ + q : ℕ) : ℝ) = (q : ℝ) * ((max C₁ C₂ : ℕ) : ℝ) + q := by rw [Nat.cast_add, Nat.cast_mul]
  rw [e, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  exact h
end MinOfBounds
