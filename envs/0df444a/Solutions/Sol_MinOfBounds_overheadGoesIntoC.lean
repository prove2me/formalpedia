-- Prove2me | solution 1 for MinOfBounds.overheadGoesIntoC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:00.730849+00:00
-- url     : https://prove2.me/submissions/7abad3a3-7242-4a98-ae75-dfc26b55e631

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
import Theorems.Thm_MinOfBounds_add_pow_le
import Theorems.Thm_MinOfBounds_exponential_part_le
import Theorems.Thm_MinOfBounds_polynomial_part_le
import Theorems.Thm_MinOfBounds_timeCor_mono

set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution : OverheadGoesIntoC := by
  intro C₁ C₂ q a
  refine ⟨q * max C₁ C₂ + q + q * 2 ^ q * (C₁ * a ^ C₁ + 2) ^ q + (a * C₁ + 1) * q, fun k m n L L₁ hk hm hn hL hL₁ => ?_⟩
  have h0 : min (timeM C₁ k m + C₁ * L₁ ^ C₁) (timeN C₂ k n) + L + 1 ≤ min (timeM C₁ k m) (timeN C₂ k n) + (C₁ * L₁ ^ C₁ + L + 1) := by omega
  calc q * (min (timeM C₁ k m + C₁ * L₁ ^ C₁) (timeN C₂ k n) + L + 1) ^ q
      ≤ q * (min (timeM C₁ k m) (timeN C₂ k n) + (C₁ * L₁ ^ C₁ + L + 1)) ^ q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h0 q)
    _ ≤ q * (2 ^ q * min (timeM C₁ k m) (timeN C₂ k n) ^ q + 2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) := Nat.mul_le_mul_left _ (add_pow_le _ _ q)
    _ = q * (2 ^ q * min (timeM C₁ k m) (timeN C₂ k n) ^ q) + q * (2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) := Nat.mul_add _ _ _
    _ ≤ timeCor (q * max C₁ C₂ + q) k m n + q * 2 ^ q * (C₁ * a ^ C₁ + 2) ^ q * L ^ ((a * C₁ + 1) * q) :=
        Nat.add_le_add (exponential_part_le C₁ C₂ q hk hm hn) (polynomial_part_le C₁ q a hL hL₁)
    _ ≤ _ := Nat.add_le_add (timeCor_mono (by omega) hk hm hn) (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hL (by omega)))
end MinOfBounds
