-- Prove2me | solution 1 for MinOfBounds.add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:04.771452+00:00
-- url     : https://prove2.me/submissions/6a714ded-677c-4dd9-9db3-d0b82c4cb82e

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

set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution (T P q : ℕ) : (T + P) ^ q ≤ 2 ^ q * T ^ q + 2 ^ q * P ^ q := by
  rcases le_total T P with h | h
  · calc (T + P) ^ q ≤ (2 * P) ^ q := Nat.pow_le_pow_left (by omega) q
      _ = 2 ^ q * P ^ q := mul_pow _ _ _
      _ ≤ _ := Nat.le_add_left _ _
  · calc (T + P) ^ q ≤ (2 * T) ^ q := Nat.pow_le_pow_left (by omega) q
      _ = 2 ^ q * T ^ q := mul_pow _ _ _
      _ ≤ _ := Nat.le_add_right _ _
end MinOfBounds
