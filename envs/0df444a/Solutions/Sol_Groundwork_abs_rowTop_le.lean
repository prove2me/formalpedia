-- Prove2me | solution 1 for Groundwork.abs_rowTop_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:08:42.788285+00:00
-- url     : https://prove2.me/submissions/d3d3be4a-1a99-4acc-9840-19cefb094ed2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
import Theorems.Thm_Groundwork_abs_prod_le_one


set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {n : ℕ} (β : Fin n → Bell) (p q : Bits n) : |rowBit.Top β p q| ≤ 1 := by
  have h : ∀ (h : Bell) (p q : Bool), |rowBit.top h p q| ≤ 1 := by decide
  exact abs_prod_le_one _ _ fun k => h _ _ _
end Groundwork
