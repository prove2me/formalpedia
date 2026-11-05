-- Prove2me | solution 1 for GeneralPieces.GenF.Y1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:34.258217+00:00
-- url     : https://prove2.me/submissions/5e6f0d58-781f-4e2f-bff5-c7075bd5bd18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_GenF_bra_coeff_outer

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (b : List ℕ) (hb : Pos b) (τ σ' : Multiset ℕ) :
    bra τ (fac (aL (xo rd) b) • coeff (aL (xo rd) b) (expW (Bp rd) * ket rd σ')) =
      ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum) :=
  bra_coeff_outer rd b hb τ σ'
end GeneralPieces.GenF
