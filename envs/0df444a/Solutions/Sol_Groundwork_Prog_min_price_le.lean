-- Prove2me | solution 1 for Groundwork.Prog.min_price_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:53.134763+00:00
-- url     : https://prove2.me/submissions/74e49c87-e184-45e7-8482-8bd651c706b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs
import Theorems.Thm_Groundwork_Prog_digit_le
import Theorems.Thm_Groundwork_GridArith_cap_pair_le
import Theorems.Thm_Groundwork_GridArith_four_mul_choose_sq_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
theorem _root_.solution (g n y : ℕ) :
    ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ) ≤ ρ * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 4 / 2 := by
  have hsum : priceRow g n y + priceCol g n y
      = 2 * ∑ q ∈ range (nRect g), (capW n (n - digit n y q) + capW n (digit n y q)) := by
    unfold priceRow priceCol
    rw [← Nat.mul_add, ← Finset.sum_add_distrib]
  have hq : ((∑ q ∈ range (nRect g), (capW n (n - digit n y q) + capW n (digit n y q)) : ℕ) : ℝ)
      ≤ (nRect g : ℝ) * (4 * ρ * n + 2) := by
    rw [Nat.cast_sum]
    calc _ ≤ ∑ _q ∈ range (nRect g), (4 * ρ * n + 2) :=
          Finset.sum_le_sum fun q _ => GridArith.cap_pair_le (digit_le n y q)
      _ = _ := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have hmin : 2 * min (priceRow g n y) (priceCol g n y) ≤ priceRow g n y + priceCol g n y := by omega
  have hmin' : 2 * ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ)
      ≤ 2 * ((∑ q ∈ range (nRect g), (capW n (n - digit n y q) + capW n (digit n y q)) : ℕ) : ℝ) := by
    rw [hsum] at hmin
    exact_mod_cast hmin
  have hR : 4 * (nRect g : ℝ) ≤ (g : ℝ) ^ 4 := by exact_mod_cast GridArith.four_mul_choose_sq_le g
  have hρ : 0 ≤ 4 * ρ * n + 2 := by
    have : 0 ≤ ρ := by unfold ρ; exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
    positivity
  have := mul_le_mul_of_nonneg_right hR hρ
  linarith
end Groundwork.Prog
