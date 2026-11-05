-- Prove2me | solution 1 for GeneralPieces.GenF.stN2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:54:01.403713+00:00
-- url     : https://prove2.me/submissions/edfcc6b3-04f7-4242-9d70-405442ede821

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_ket
import Theorems.Thm_GeneralPieces_GenF_bra_prod_tT
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_braW
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_expD
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_expW


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution : StN2 := by
  intro rd E σ σ'
  rw [normal, constantCoeff_braW, map_mul, map_mul, constantCoeff_expW (X := X) (R := Tv), constantCoeff_expW (X := X) (R := Tv), one_mul, one_mul, Phi,
    constantCoeff_expD (X := X) (A := Tv), constantCoeff_ket, bra_prod_tT]
end GeneralPieces.GenF
