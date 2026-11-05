-- Prove2me | solution 1 for GeneralPieces.GenF.DD_xi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:26.733538+00:00
-- url     : https://prove2.me/submissions/35665ff6-c469-40a8-b623-8a6b57ac6f7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
import Theorems.Thm_GeneralPieces_GenF_sel_xi


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) {n : ℕ} (hn : 1 ≤ n) : DD rd (xi rd n) = JmT n := sel_xi rd JmT 0 hn
end GeneralPieces.GenF
