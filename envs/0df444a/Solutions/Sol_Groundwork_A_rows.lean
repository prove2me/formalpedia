-- Prove2me | solution 1 for Groundwork.A_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:58.532291+00:00
-- url     : https://prove2.me/submissions/fbf31795-508f-4ac5-b2c0-fe296b0665da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
import Theorems.Thm_Groundwork_BitCut_expand
import Theorems.Thm_Groundwork_rowBot_eq_zero

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution (n i : ℕ) (x y u v : Bits n) :
    A n i x y u v = ∑ β ∈ rowLabels n i, rowBit.Top β x y * rowBit.Bot i β u v := by
  have h := rowBit.expand (fun a b c' d => I₁ a b c' d) (fun a b c' d => -(s a b * s c' d))
    (by decide) (by decide) i x y u v
  refine (h.trans (sum_subset (subset_univ _) fun β _ hβ => ?_).symm)
  rw [rowBot_eq_zero (by simpa [rowLabels] using hβ), mul_zero]
end Groundwork
