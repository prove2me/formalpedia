-- Prove2me | solution 1 for GeneralPieces.GenF.Phi_embW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:58:30.169535+00:00
-- url     : https://prove2.me/submissions/e31c87f9-4d81-4f88-800c-63f0360381d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_Normal_DD_emb
import Theorems.Thm_GeneralPieces_GenF_expD_of_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (e : PS) : Phi rd (embW e) = embW e := by
  rw [Phi, expD_of_zero (X := X) (A := Tv) (DD rd)]
  intro i α
  rw [embW, MvPowerSeries.coeff_map, Normal.DD_emb]
end GeneralPieces.GenF
