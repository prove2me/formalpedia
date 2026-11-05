-- Prove2me | solution 1 for GeneralPieces.Group.card_events_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:27.533854+00:00
-- url     : https://prove2.me/submissions/938440b3-6f29-42b6-b62d-dbc024cd12f5

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
theorem _root_.solution {K g : ℕ} (hK : 1 ≤ K) (hg : 2 ≤ g) : (g + 1) * K < 2 * g * K :=
  Nat.mul_lt_mul_of_pos_right (by omega) hK
end GeneralPieces.Group
