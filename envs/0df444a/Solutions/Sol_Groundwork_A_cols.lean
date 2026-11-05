-- Prove2me | solution 1 for Groundwork.A_cols
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:10:01.535963+00:00
-- url     : https://prove2.me/submissions/ceb390c6-a4c5-4479-a7cc-b455d4ef604b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
import Theorems.Thm_Groundwork_BitCut_expand
import Theorems.Thm_Groundwork_colBot_eq_zero

set_option autoImplicit false
section
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution (n i : ℕ) (x y u v : Bits n) :
    A n i x y u v = ∑ β ∈ colLabels n i, colBit.Top β x u * colBit.Bot i β y v := by
  have h := colBit.expand (fun a b c' d => I₁ a c' b d) (fun a b c' d => -(s a c' * s b d))
    (by decide) (by decide) i x u y v
  refine (h.trans (sum_subset (subset_univ _) fun β _ hβ => ?_).symm)
  rw [colBot_eq_zero (by simpa [colLabels] using hβ), mul_zero]
end Groundwork
