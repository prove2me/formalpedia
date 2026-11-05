-- Prove2me | solution 1 for GeneralPieces.GenF.Phi_expW_Bp_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:57:13.177073+00:00
-- url     : https://prove2.me/submissions/bfab864d-4699-4fd1-a3e8-5934016c169f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
import Theorems.Thm_GeneralPieces_GenF_Phi_Bp
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_embW_kap
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_lin
import Theorems.Thm_GeneralPieces_GenF_expD_expW
import Theorems.Thm_GeneralPieces_GenF_expW_add
import Theorems.Thm_GeneralPieces_GenF_map_expW


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (w : W) : Phi rd (expW (Bp rd) * w) = embW (expW (kap rd)) * (expW (Bp rd) * Phi rd w) := by
  have h0 : constantCoeff (Bp rd) = 0 := constantCoeff_lin (X := X) (A := Tv) _
  have h1 := expD_expW (X := X) (A := Tv) (w := Bp rd) (DD rd) h0
  have h2 : Phi rd (expW (Bp rd)) = expW (Phi rd (Bp rd)) := h1
  have h3 := expW_add (X := X) (R := Tv) h0 (constantCoeff_embW_kap rd)
  have h4 := map_expW (X := X) (R := S) (R' := Tv) emb (kap rd)
  have h5 : embW (expW (kap rd)) = expW (embW (kap rd)) := h4
  rw [map_mul, h2, Phi_Bp, h3, h5]
  ring
end GeneralPieces.GenF
