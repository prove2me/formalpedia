-- Prove2me | solution 1 for GeneralPieces.GenF.DD_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:39:07.50803+00:00
-- url     : https://prove2.me/submissions/aaea4d4b-9ea0-4bcb-b7f1-7b39c7fdbde3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
import Theorems.Thm_GeneralPieces_GenF_DD_xi
import Theorems.Thm_GeneralPieces_GenF_DD_xo
import Theorems.Thm_GeneralPieces_GenF_sel_xi_zero
import Theorems.Thm_GeneralPieces_GenF_xi_or_xo


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (i : X) : DD rd i = 0 ∨ ∃ n, DD rd i = JmT n := by
  rcases xi_or_xo rd i with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · by_cases hn : n = 0
    · subst hn
      exact Or.inl (sel_xi_zero rd JmT 0)
    · exact Or.inr ⟨n, DD_xi rd (by omega)⟩
  · exact Or.inl (DD_xo rd n)
end GeneralPieces.GenF
