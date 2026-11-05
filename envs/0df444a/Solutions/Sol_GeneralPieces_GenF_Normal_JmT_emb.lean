-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.JmT_emb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:55:57.626978+00:00
-- url     : https://prove2.me/submissions/eb4a4790-afff-47f9-9b74-1a2fa36a08d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_coeff_hder


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
namespace Normal
theorem _root_.solution (n : ℕ) (s : S) : JmT n (emb s) = 0 := by
  refine HahnSeries.ext (funext fun y => ?_)
  rw [JmT, coeff_hder]
  exact MvPolynomial.derivation_C (JmU n) (s.coeff y)
end Normal
end GeneralPieces.GenF
