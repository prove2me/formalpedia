-- Prove2me | solution 1 for Groundwork.abs_rowBot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:50.988753+00:00
-- url     : https://prove2.me/submissions/c7c0be5a-3785-471c-8001-3a7e67670837

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
import Theorems.Thm_Groundwork_abs_sum_powersetCard_le


set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {n : ℕ} (i : ℕ) (β : Fin n → Bell) (p q : Bits n) : |rowBit.Bot i β p q| ≤ 2 ^ n := by
  have h1 : ∀ (h : Bell) (p q : Bool), |rowBit.bot1 h p q| ≤ 1 := by decide
  have h0 : ∀ (h : Bell) (p q : Bool), |rowBit.bot0 h p q| ≤ 1 := by decide
  exact abs_sum_powersetCard_le i _ _ (fun k => h1 _ _ _) fun k => h0 _ _ _
end Groundwork
