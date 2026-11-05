-- Prove2me | solution 1 for Groundwork.abs_A_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:03.214551+00:00
-- url     : https://prove2.me/submissions/bb773b12-bbd0-485f-9243-ee2618f90448

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit
import Theorems.Thm_Groundwork_abs_sum_powersetCard_le

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution (n i : ℕ) (x y u v : Bits n) : |A n i x y u v| ≤ 2 ^ n := by
  have h1 : ∀ p q a b : Bool, |(-(s p q * s a b))| ≤ 1 := by decide
  have h0 : ∀ p q a b : Bool, |I₁ p q a b| ≤ 1 := by decide
  exact abs_sum_powersetCard_le i _ _ (fun k => h1 (x k) (y k) (u k) (v k)) fun k => h0 (x k) (y k) (u k) (v k)
end Groundwork
