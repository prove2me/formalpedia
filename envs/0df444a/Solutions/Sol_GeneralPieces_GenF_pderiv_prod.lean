-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:56:26.962796+00:00
-- url     : https://prove2.me/submissions/99d5ec09-a0dc-41ec-b245-e574aa782f16

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_DD_comm
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_lin
import Theorems.Thm_GeneralPieces_GenF_pderiv_expD
import Theorems.Thm_GeneralPieces_GenF_pderiv_expW
import Theorems.Thm_GeneralPieces_GenF_pderiv_lin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (E : ℕ) (i : X) (w : W) : MvPowerSeries.pderiv Tv i (expW (Ap rd E) * Phi rd w) =
    MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) 0 i) * (expW (Ap rd E) * Phi rd w) +
      expW (Ap rd E) * (Phi rd (MvPowerSeries.pderiv Tv i w) + Phi rd (mapD (DD rd i) w)) := by
  have h1 : MvPowerSeries.pderiv Tv i (expW (Ap rd E)) = MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) 0 i) * expW (Ap rd E) := by
    rw [pderiv_expW (A := Tv) i (w := Ap rd E) (constantCoeff_lin _), Ap, pderiv_lin (A := Tv) _ i]
  have h2 : MvPowerSeries.pderiv Tv i (Phi rd w) = Phi rd (MvPowerSeries.pderiv Tv i w) + Phi rd (mapD (DD rd i) w) := pderiv_expD (DD_comm rd) i w
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h1, h2]
  ring
end GeneralPieces.GenF
