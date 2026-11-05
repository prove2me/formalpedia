-- Prove2me | solution 1 for GeneralPieces.GenF.pderiv_normal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:03:00.146181+00:00
-- url     : https://prove2.me/submissions/48379bc1-ac7f-44bf-96bc-47d971a28713

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
import Theorems.Thm_GeneralPieces_GenF_Normal_C_rat_smul
import Theorems.Thm_GeneralPieces_GenF_pderiv_three
import Theorems.Thm_GeneralPieces_GenF_Normal_sel_add
import Theorems.Thm_GeneralPieces_GenF_pderiv_Phi_ket
import Theorems.Thm_GeneralPieces_GenF_braW_C_sel_mul
import Theorems.Thm_GeneralPieces_GenF_braW_embW_mul
import Theorems.Thm_GeneralPieces_GenF_braW_smul
import Theorems.Thm_GeneralPieces_GenF_braW_sum
import Theorems.Thm_GeneralPieces_GenF_constantCoeff_lin
import Theorems.Thm_GeneralPieces_GenF_pderiv_braW
import Theorems.Thm_GeneralPieces_GenF_pderiv_lin


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
namespace GeneralPieces.GenF
theorem _root_.solution (rd : Bool) {E : ℕ} {σ : Multiset ℕ} (hσ : σ.sum ≤ E) (σ' : Multiset ℕ) (i : X) :
    MvPowerSeries.pderiv S i (normal rd E σ σ') =
      ∑ l ∈ σ.toFinset, MvPowerSeries.C (cS rd i (l : ℤ)) * normal rd E (σ.erase l) σ' +
        ∑ k ∈ σ'.toFinset, MvPowerSeries.C (((k : ℚ) * σ'.count k) • cS rd i (-(k : ℤ))) * normal rd E σ (σ'.erase k) := by
  have hp : MvPowerSeries.pderiv Tv i (Ap rd E) + MvPowerSeries.pderiv Tv i (Bp rd) = MvPowerSeries.C (sel rd (fun n => HahnSeries.C (JpU E n)) JpV i) := by
    rw [Ap, Bp, pderiv_lin (X := X) (A := Tv), pderiv_lin (X := X) (A := Tv), ← map_add, Normal.sel_add]
  rw [normal, pderiv_braW, pderiv_three (Y := X) (A := Tv) i (by rw [Ap, constantCoeff_lin (X := X) (A := Tv)]) (by rw [Bp, constantCoeff_lin (X := X) (A := Tv)]), hp,
    pderiv_Phi_ket, braW_add, braW_C_sel_mul rd hσ, Finset.mul_sum, Finset.mul_sum, braW_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, braW_smul, mul_left_comm (expW (Bp rd)), mul_left_comm (expW (Ap rd E)), braW_embW_mul,
    mul_comm (k : ℚ), ← smul_smul, Normal.C_rat_smul (Y := X) (A := S) (σ'.count k : ℚ), smul_mul_assoc, normal]
end GeneralPieces.GenF
