-- Prove2me | solution 1 for GeneralPieces.Group.tot_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:26.515529+00:00
-- url     : https://prove2.me/submissions/75c9cceb-081d-465a-9cb2-473fdd383366

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_GeneralPieces_Group_cs_eq

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution {g : ℕ} (c : Fin g → Fin g → ℕ) : tot c = ∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ) := sum_congr rfl fun a _ => cs_eq c a
end GeneralPieces.Group
