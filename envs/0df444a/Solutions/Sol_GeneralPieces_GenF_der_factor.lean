-- Prove2me | solution 1 for GeneralPieces.GenF.der_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:00:26.552563+00:00
-- url     : https://prove2.me/submissions/8327c0f9-607f-473c-9d13-a2a079db8658

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_Normal_mapD_C
import Theorems.Thm_GeneralPieces_GenF_Normal_pderiv_rat_smul
import Theorems.Thm_GeneralPieces_GenF_Normal_C_rat_smul
import Theorems.Thm_GeneralPieces_GenF_Normal_sel_add
import Theorems.Thm_GeneralPieces_GenF_Normal_mapD_embW
import Theorems.Thm_GeneralPieces_GenF_Normal_emb_rat_smul
import Theorems.Thm_GeneralPieces_GenF_DD_tT
import Theorems.Thm_GeneralPieces_GenF_map_lin
import Theorems.Thm_GeneralPieces_GenF_pderiv_lin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (i : X) (k : ℕ) :
    MvPowerSeries.pderiv Tv i (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) + mapD (DD rd i) (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) =
      embW (MvPowerSeries.C ((k : ℚ) • cS rd i (-(k : ℤ)))) := by
  have h1 : MvPowerSeries.pderiv Tv i (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) =
      embW (MvPowerSeries.C ((k : ℚ) • sel rd 0 (fun n => (bet n (-(k : ℤ)) : ℚ) • mo 0 (-(k : ℤ) - n)) i)) := by
    rw [map_add, MvPowerSeries.pderiv_C, zero_add, Normal.pderiv_rat_smul (Y := X) (A := Tv), sfB', embW, map_lin (Y := X) (A := S) (A' := Tv),
      pderiv_lin (X := X) (A := Tv), MvPowerSeries.map_C, Normal.emb_rat_smul, Normal.C_rat_smul (Y := X) (A := Tv)]
  have h2 : mapD (DD rd i) (MvPowerSeries.C (tT k) + (k : ℚ) • embW (sfB' rd k)) =
      embW (MvPowerSeries.C ((k : ℚ) • sel rd (fun n => (bet n (-(k : ℤ)) : ℚ) • mo (-(k : ℤ) - n) 0) 0 i)) := by
    rw [map_add, map_smul, Normal.mapD_embW, smul_zero, add_zero, embW, MvPowerSeries.map_C, ← DD_tT, Normal.mapD_C (Y := X) (A := Tv)]
  rw [h1, h2, ← map_add, ← map_add, ← smul_add, add_comm, Normal.sel_add, cS]
end GeneralPieces.GenF
