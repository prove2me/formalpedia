-- Prove2me | solution 1 for GeneralPieces.Sizes.p_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:27:14.850583+00:00
-- url     : https://prove2.me/submissions/c8215823-f22d-44fe-96b5-99269a9d05b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Ring_Bd_mono
import Theorems.Thm_GeneralPieces_ptnFacts


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {E E' : ℕ} (hE : E ≤ E') : Partitions.p E ≤ Partitions.p E' := monotone_nat_of_le_succ ptnFacts.mono hE
end GeneralPieces.Sizes
