-- Prove2me | solution 1 for GeneralPieces.GenF.JmT_emb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:52:05.824795+00:00
-- url     : https://prove2.me/submissions/9fcddd2b-9020-4b57-b83e-df28957c2380

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
theorem _root_.solution (p : ℕ) (s : S) : JmT p (emb s) = 0 := by
  refine HahnSeries.ext (funext fun y => ?_)
  show JmU p (MvPolynomial.C (s.coeff y)) = 0
  exact (JmU p).map_algebraMap (s.coeff y)
end GeneralPieces.GenF
