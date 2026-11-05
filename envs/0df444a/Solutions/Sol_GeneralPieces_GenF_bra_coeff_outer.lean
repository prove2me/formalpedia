-- Prove2me | solution 1 for GeneralPieces.GenF.bra_coeff_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:25.288204+00:00
-- url     : https://prove2.me/submissions/7b2e137d-0b64-47e1-a567-8718154951e5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_GenF_Yent_nil
import Theorems.Thm_GeneralPieces_GenF_Yent_cons
import Theorems.Thm_GeneralPieces_GenF_Y_mo_zero_mul
import Theorems.Thm_GeneralPieces_GenF_Y_aL_nil
import Theorems.Thm_GeneralPieces_GenF_Y_aL_cons
import Theorems.Thm_GeneralPieces_GenF_Y_constantCoeff_outer
import Theorems.Thm_GeneralPieces_GenF_pderiv_xo_outer
import Theorems.Thm_GeneralPieces_GenF_borel_step
import Theorems.Thm_GeneralPieces_GenF_bra_JpV_mul
import Theorems.Thm_GeneralPieces_GenF_bra_emb_mul
import Theorems.Thm_GeneralPieces_GenF_bra_prod_tT
import Theorems.Thm_GeneralPieces_GenF_bra_sum
import Theorems.Thm_GeneralPieces_GenF_fac_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) (b : List ℕ) (hb : Pos b) (τ σ' : Multiset ℕ) :
    bra τ (fac (aL (xo rd) b) • coeff (aL (xo rd) b) (outer rd σ')) = Yent (mo 0) b τ σ' := by
  induction b generalizing τ σ' with
  | nil => rw [aL_nil, fac_zero, one_smul, coeff_zero_eq_constantCoeff_apply, constantCoeff_outer, bra_prod_tT, Yent_nil _ mo_zero]
  | cons n b ih =>
    have hn : 1 ≤ n := hb n List.mem_cons_self
    have hb' : Pos b := fun m hm => hb m (List.mem_cons_of_mem _ hm)
    rw [aL_cons, borel_step (aL (xo rd) b) (xo rd n) (outer rd σ'), pderiv_xo_outer rd hn, map_add, map_sum, coeff_C_mul, smul_add, Finset.smul_sum, bra_add, bra_sum, ← mul_smul_comm, bra_JpV_mul,
      Yent_cons _ mo_zero_mul]
    apply congrArg₂ (· + ·)
    · exact Finset.sum_congr rfl fun l _ => by rw [ih hb']
    · exact Finset.sum_congr rfl fun k _ => by rw [coeff_C_mul, ← mul_smul_comm, bra_emb_mul, ih hb']
end GeneralPieces.GenF
