-- Prove2me | solution 1 for GeneralPieces.Group.cz_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:54:12.722957+00:00
-- url     : https://prove2.me/submissions/91030839-8e7e-4521-889c-0847d9d89f6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution {g : ℕ} (c : Fin g → Fin g → ℕ) (a b : Fin g) : 0 ≤ cz c a b := by
  unfold cz; split_ifs
  · exact le_rfl
  · exact Nat.cast_nonneg _
end GeneralPieces.Group
