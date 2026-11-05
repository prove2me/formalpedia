-- Prove2me | solution 1 for GeneralPieces.GenF.constantCoeff_ket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:29.916582+00:00
-- url     : https://prove2.me/submissions/e6aa20db-b8f0-4171-8c14-30da695703fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
import Theorems.Thm_GeneralPieces_GenF_coeff_rat_smul
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_lin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (σ' : Multiset ℕ) : MvPowerSeries.constantCoeff (ket rd σ') = (σ'.map tT).prod := by
  unfold ket
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun k _ => ?_
  have e : MvPowerSeries.constantCoeff ((k : ℚ) • embW (sfB' rd k)) = (k : ℚ) • MvPowerSeries.constantCoeff (embW (sfB' rd k)) :=
    coeff_rat_smul (X := X) (R := Tv) 0 _ _
  rw [Function.comp_apply, map_add, MvPowerSeries.constantCoeff_C, e, embW, MvPowerSeries.constantCoeff_map, sfB', constantCoeff_lin, map_zero, smul_zero, add_zero]
end GeneralPieces.GenF
