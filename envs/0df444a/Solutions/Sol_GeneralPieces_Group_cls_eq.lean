-- Prove2me | solution 1 for GeneralPieces.Group.cls_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:52:36.852916+00:00
-- url     : https://prove2.me/submissions/8471203e-77a8-47c2-8eae-89a6cf4ef27b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_ClauseBound_Group_Grouping_mem_cls


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : cls e γ = ({a | chi0 (e a) = γ} : Finset (Fin (K * n))) := by
  ext a
  rw [mem_cls, mem_filter, and_iff_right (mem_univ a)]
end GeneralPieces.Group
