-- Prove2me | solution 1 for GeneralPieces.Bits.pZ_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:28:35.693644+00:00
-- url     : https://prove2.me/submissions/806a0d2d-2269-4293-9a22-2facfc66e62b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_ClauseBound_Part_p_mono
import Theorems.Thm_GeneralPieces_Sizes_p_mono


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution {E E' : ℤ} (h : E ≤ E') : pZ E ≤ pZ E' := by
  unfold pZ
  split_ifs
  · exact p_mono (by omega)
  · omega
  · exact Nat.zero_le _
  · exact le_rfl
end GeneralPieces.Bits
