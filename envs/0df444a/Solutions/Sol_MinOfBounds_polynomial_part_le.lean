-- Prove2me | solution 1 for MinOfBounds.polynomial_part_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:07.003193+00:00
-- url     : https://prove2.me/submissions/641cea52-a828-49fc-8f25-15e65e368f32

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution (C₁ q a : ℕ) {L L₁ : ℕ} (hL : 1 ≤ L) (h : L₁ ≤ a * L ^ a) :
    q * (2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) ≤ q * 2 ^ q * (C₁ * a ^ C₁ + 2) ^ q * L ^ ((a * C₁ + 1) * q) := by
  have h1 : L₁ ^ C₁ ≤ a ^ C₁ * L ^ (a * C₁) := (Nat.pow_le_pow_left h C₁).trans_eq (by rw [mul_pow, ← pow_mul])
  have h2 : L ^ (a * C₁) ≤ L ^ (a * C₁ + 1) := Nat.pow_le_pow_right hL (Nat.le_succ _)
  have h3 : L ≤ L ^ (a * C₁ + 1) := Nat.le_self_pow (Nat.succ_ne_zero _) L
  have h4 : 1 ≤ L ^ (a * C₁ + 1) := Nat.one_le_pow _ _ hL
  have h5 : C₁ * L₁ ^ C₁ + L + 1 ≤ (C₁ * a ^ C₁ + 2) * L ^ (a * C₁ + 1) := by
    calc C₁ * L₁ ^ C₁ + L + 1 ≤ C₁ * (a ^ C₁ * L ^ (a * C₁ + 1)) + L ^ (a * C₁ + 1) + L ^ (a * C₁ + 1) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2))) h3) h4
      _ = _ := by ring
  calc q * (2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) ≤ q * (2 ^ q * ((C₁ * a ^ C₁ + 2) * L ^ (a * C₁ + 1)) ^ q) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 q))
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      ring
end MinOfBounds
