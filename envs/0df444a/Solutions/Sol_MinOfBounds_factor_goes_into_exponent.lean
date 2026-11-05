-- Prove2me | solution 1 for MinOfBounds.factor_goes_into_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:05.848795+00:00
-- url     : https://prove2.me/submissions/40926ed6-9fbd-4ad6-a87f-9b3418fef850

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
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper
namespace MinOfBounds
theorem _root_.solution (q D T : ℕ) {X : ℝ} (hX : 2 ≤ X) (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((D : ℝ) * X)) :
    (q : ℝ) * ((2 : ℝ) ^ q * (T : ℝ) ^ q) ≤ (2 : ℝ) ^ (((q : ℝ) * D + q) * X) := by
  have h1 : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast Nat.lt_two_pow_self.le
  have h2 : (q : ℝ) * (2 : ℝ) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * X) := by
    calc (q : ℝ) * (2 : ℝ) ^ q ≤ (2 : ℝ) ^ q * (2 : ℝ) ^ q := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 : ℝ) ^ ((q : ℝ) * 2) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast, Real.rpow_two]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg q))
  have h3 : (T : ℝ) ^ q ≤ (2 : ℝ) ^ ((q : ℝ) * ((D : ℝ) * X)) := by
    calc (T : ℝ) ^ q ≤ ((2 : ℝ) ^ ((D : ℝ) * X)) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg T) hT q
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
  calc (q : ℝ) * ((2 : ℝ) ^ q * (T : ℝ) ^ q) = (q : ℝ) * (2 : ℝ) ^ q * (T : ℝ) ^ q := by ring
    _ ≤ (2 : ℝ) ^ ((q : ℝ) * X) * (2 : ℝ) ^ ((q : ℝ) * ((D : ℝ) * X)) := mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add two_pos]
      congr 1
      ring
end MinOfBounds
