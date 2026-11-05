-- Prove2me | solution 2 for GeneralPieces.ThmHalfPieces.sq_le_eR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:33:35.188421+00:00
-- url     : https://prove2.me/submissions/56206d5f-12ed-44e9-9cde-b66471dd625a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bits
import Definitions.Def_ClauseBound_Boson_Final
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.ThmHalfPieces
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes GeneralPieces.Lex
namespace GeneralPieces.ThmHalfPieces
theorem _root_.solution (h : ℕ) : h * h + 12 * h ^ 2 ≤ ClauseBound.Boson.Half.eR h := by
  unfold ClauseBound.Boson.Half.eR
  nlinarith
end GeneralPieces.ThmHalfPieces
