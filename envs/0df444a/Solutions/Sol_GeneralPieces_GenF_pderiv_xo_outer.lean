-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_xo_outer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:51:55.883677+00:00
-- url     : https://prove2.me/submissions/4f50a856-d9b5-4705-a59f-fbda75684f05

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
import Theorems.Thm_GeneralPieces_GenF_sel_xo


set_option maxHeartbeats 200000
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
namespace GeneralPieces.GenF
attribute [local irreducible] expW outer JpV emb
theorem _root_.solution (rd : Bool) {n : ℕ} (hn : 1 ≤ n) (σ' : Multiset ℕ) :
    pderiv Tv (xo rd n) (outer rd σ') = C (JpV n) * outer rd σ' +
      ∑ k ∈ σ'.toFinset, C (emb (((k : ℚ) * σ'.count k * bet n (-(k : ℤ))) • mo 0 (-(k : ℤ) - n))) * outer rd (σ'.erase k) := by
  unfold outer
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_expW (xo rd n) (w := Bp rd) (constantCoeff_lin _), Bp, pderiv_lin, sel_xo rd _ _ hn, pderiv_ket, Finset.mul_sum, add_comm]
  apply congrArg₂ (· + ·)
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [cB, sel_xo rd _ _ hn, smul_smul]
    ac_rfl
end GeneralPieces.GenF
