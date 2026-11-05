-- Prove2me | solution 1 for GeneralPieces.Group.card_group
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:07.743514+00:00
-- url     : https://prove2.me/submissions/8fd5d803-2c92-4b16-9477-9827f7d48602

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_GeneralPieces_Group_cls_eq
import Theorems.Thm_ClauseBound_Group_Grouping_card_cls


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : #{a | chi0 (e a) = γ} = n := by rw [← cls_eq, card_cls]
end GeneralPieces.Group
