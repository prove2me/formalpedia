-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.DD_emb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:57:01.64356+00:00
-- url     : https://prove2.me/submissions/3d1da1e3-17ec-46b2-98d7-f26f0ea7cbc2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_Normal_JmT_emb
import Theorems.Thm_GeneralPieces_GenF_DD_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
namespace Normal
theorem _root_.solution (rd : Bool) (i : X) (s : S) : DD rd i (emb s) = 0 := by
  rcases DD_eq rd i with h | ⟨n, h⟩
  · rw [h]
    rfl
  · rw [h, Normal.JmT_emb]
end Normal
end GeneralPieces.GenF
