-- Prove2me | solution 1 for Groundwork.abs_sum_powersetCard_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:45.133659+00:00
-- url     : https://prove2.me/submissions/76bbc827-97ea-4909-91f3-4c6383ab97a6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit
import Theorems.Thm_Groundwork_abs_prod_le_one

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {n : ℕ} (i : ℕ) (f1 f0 : Fin n → ℤ) (h1 : ∀ k, |f1 k| ≤ 1) (h0 : ∀ k, |f0 k| ≤ 1) :
    |∑ S ∈ powersetCard i (univ : Finset (Fin n)), (∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k| ≤ 2 ^ n := by
  calc |∑ S ∈ powersetCard i (univ : Finset (Fin n)), (∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k|
      ≤ ∑ S ∈ powersetCard i (univ : Finset (Fin n)), |(∏ k ∈ S, f1 k) * ∏ k ∈ Sᶜ, f0 k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ powersetCard i (univ : Finset (Fin n)), (1 : ℤ) := by
        refine sum_le_sum fun S _ => ?_
        rw [abs_mul]
        exact mul_le_one₀ (abs_prod_le_one S f1 h1) (abs_nonneg _) (abs_prod_le_one Sᶜ f0 h0)
    _ = (n.choose i : ℤ) := by simp
    _ ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
end Groundwork
