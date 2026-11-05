-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_xi_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:04:17.725206+00:00
-- url     : https://prove2.me/submissions/48c962fd-5e99-4e8a-9993-9555416f4481

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_GenF_Y_pderiv_ket
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_lin
import Theorems.Thm_GeneralPieces_GenF_pderiv_expW
import Theorems.Thm_GeneralPieces_GenF_pderiv_lin
import Theorems.Thm_GeneralPieces_GenF_sel_zero_xi


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (n : ℕ) (σ' : Multiset ℕ) : pderiv Tv (xi rd n) (outer rd σ') = 0 := by
  rw [outer, Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_expW (xi rd n) (w := Bp rd) (constantCoeff_lin _), Bp, pderiv_lin, sel_zero_xi, pderiv_ket, map_zero, zero_mul, mul_zero, add_zero,
    Finset.sum_eq_zero fun k _ => by rw [cB, sel_zero_xi, smul_zero, map_zero, map_zero, zero_mul], mul_zero]
end GeneralPieces.GenF
