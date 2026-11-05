-- Prove2me | solution 1 for GeneralPieces.Group.cs_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:25.422072+00:00
-- url     : https://prove2.me/submissions/39f0c6ab-ff1d-4e04-b7f7-78e7db6816bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_GeneralPieces_Group_cz_nonneg

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution {g : ℕ} (c : Fin g → Fin g → ℕ) (a : Fin g) : 0 ≤ cs c a := sum_nonneg fun b _ => cz_nonneg c a b
end GeneralPieces.Group
