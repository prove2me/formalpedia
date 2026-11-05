-- Prove2me | solution 1 for Groundwork.abs_prod_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:36.384369+00:00
-- url     : https://prove2.me/submissions/f0517313-cd51-491d-9df0-85912fcc3c92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_prod_le_prod_of_nonneg

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
namespace Groundwork
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℤ) {B k : ℕ} (h : ∀ i ∈ s, |f i| ≤ 2 ^ B)
    (hk : #s ≤ k) : |∏ i ∈ s, f i| ≤ 2 ^ (B * k) := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, (2 : ℤ) ^ B := prod_le_prod_of_nonneg _ _ _ (fun _ _ => abs_nonneg _) h
    _ = 2 ^ (B * #s) := by rw [Finset.prod_const, pow_mul]
    _ ≤ 2 ^ (B * k) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hk)
end Groundwork
