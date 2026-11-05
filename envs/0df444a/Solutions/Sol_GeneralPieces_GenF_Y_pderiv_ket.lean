-- Prove2me | solution 1 for GeneralPieces.GenF.Y.pderiv_ket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:02:42.128366+00:00
-- url     : https://prove2.me/submissions/9c693380-485c-4d41-a751-2150325bc969

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_GenF_Y_der_prod
import Theorems.Thm_GeneralPieces_GenF_Y_C_rat_smul
import Theorems.Thm_GeneralPieces_GenF_Y_emb_rat_smul
import Theorems.Thm_GeneralPieces_GenF_Y_pderiv_factor

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y
namespace GeneralPieces.GenF.Y
theorem _root_.solution (rd : Bool) (i : X) (σ' : Multiset ℕ) :
    pderiv Tv i (ket rd σ') = ∑ k ∈ σ'.toFinset, C (emb (((k : ℚ) * σ'.count k) • cB rd k i)) * ket rd (σ'.erase k) := by
  rw [ket, der_prod (R := Tv) (B := W) (pderiv Tv i) σ']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_factor, ← Nat.cast_smul_eq_nsmul ℚ, ← smul_mul_assoc, ← C_rat_smul (R := Tv), ← emb_rat_smul, smul_smul, mul_comm (σ'.count k : ℚ), ket]
end GeneralPieces.GenF.Y
