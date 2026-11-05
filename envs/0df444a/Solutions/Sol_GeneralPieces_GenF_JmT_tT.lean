-- Prove2me | solution 1 for GeneralPieces.GenF.JmT_tT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:57:49.296775+00:00
-- url     : https://prove2.me/submissions/7e687e63-2553-4b26-8264-cf7d4b801cc5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_Normal_emb_smul_mo
import Theorems.Thm_GeneralPieces_GenF_hder_C


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (n k : ℕ) : JmT n (tT k) = emb ((k : ℚ) • ((bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0)) := by
  rw [smul_smul, Normal.emb_smul_mo, JmT, tT, hder_C]
  congr 1
  exact MvPolynomial.mkDerivation_X _ _ _
end GeneralPieces.GenF
