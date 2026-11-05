-- Prove2me | solution 1 for Groundwork.abs_prod_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:25.215502+00:00
-- url     : https://prove2.me/submissions/962df350-bf50-4d35-96e5-541270083d1e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Groundwork_Cross_Bit

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {ι : Type} (S : Finset ι) (f : ι → ℤ) (h : ∀ k, |f k| ≤ 1) : |∏ k ∈ S, f k| ≤ 1 := by
  rw [abs_prod]
  exact prod_le_one (fun _ _ => abs_nonneg _) fun k _ => h k
end Groundwork
