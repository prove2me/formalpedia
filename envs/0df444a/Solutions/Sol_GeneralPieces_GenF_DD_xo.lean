-- Prove2me | solution 1 for GeneralPieces.GenF.DD_xo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:27.803059+00:00
-- url     : https://prove2.me/submissions/c83af6c3-bd9b-4993-9c1a-5dd13c65dc63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
import Theorems.Thm_P2M_GeneralPieces_GenF_sel_xo__1f77a7ff0981


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (n : ℕ) : DD rd (xo rd n) = 0 := by
  rw [DD, sel_xo']
  unfold z0
  split_ifs <;> rfl
end GeneralPieces.GenF
