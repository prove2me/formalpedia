-- Prove2me | solution 1 for Groundwork.Sparsify.polyT_greedyP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:34:08.570126+00:00
-- url     : https://prove2.me/submissions/35cb81e0-b80c-499b-a4c1-c9e4943d0696

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Sparsify
import Theorems.Thm_P2M_Groundwork_Sparsify_polyT_greedyP__a113a83293ad

set_option autoImplicit false
section
section
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]
namespace Groundwork.Sparsify
theorem _root_.solution (k : ℕ) {used : α → PCl} {l : α → PFml} (hu : PolyT used) (hl : PolyT l) :
    PolyT fun x => greedyP k (used x) (l x) := polyT_greedyP' k hu hl
end Groundwork.Sparsify
