-- Prove2me | solution 1 for GeneralPieces.GenF.Normal.emb_rat_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:56:36.853603+00:00
-- url     : https://prove2.me/submissions/f5e03040-e050-4e1b-b5a1-999d3b75e03d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
namespace Normal
theorem _root_.solution (q : ℚ) (s : S) : emb (q • s) = q • emb s := by
  refine HahnSeries.ext (funext fun y => ?_)
  show MvPolynomial.C (q • s.coeff y) = q • MvPolynomial.C (s.coeff y)
  exact map_rat_smul (MvPolynomial.C : Lu →+* Vu) q _
end Normal
end GeneralPieces.GenF
