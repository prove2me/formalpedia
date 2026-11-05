-- Prove2me | solution 1 for GeneralPieces.Half.botK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:42:00.847139+00:00
-- url     : https://prove2.me/submissions/eec3e55c-2432-4359-8228-0ec8fbf27311

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
import Theorems.Thm_GeneralPieces_Half_toL_toPNats
import Theorems.Thm_GeneralPieces_Half_toN_ptn
import Theorems.Thm_GeneralPieces_Half_wt_ptn
import Theorems.Thm_GeneralPieces_Half_zz_eq
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_ClauseBound_Boson_zz_dvd_factorial
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_op_smul_left
import Theorems.Thm_GeneralPieces_Ring_op_tpow
import Theorems.Thm_GeneralPieces_stBridge


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half
namespace GeneralPieces.Half
theorem _root_.solution {L : List ℕ} {h : ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (r : ℤ) (π σ : Ptn) :
    ((ClauseBound.Boson.botK L h r (toN π) (toN σ) : ℤ) : ℚ) = coef π (op (bFam (ptn L)) r (tpow σ)) := by
  have hd : ClauseBound.Boson.zz (L : Multiset ℕ) ∣ h.factorial :=
    ClauseBound.Boson.zz_dvd_factorial (⟨(L : Multiset ℕ), fun hi => hL _ (Multiset.mem_coe.1 hi), by rw [Multiset.sum_coe]; exact hs⟩ : Nat.Partition h)
  have h0 : ((ClauseBound.Boson.zz (L : Multiset ℕ) : ℕ) : ℚ) ≠ 0 := by
    intro h0
    have h1 : ClauseBound.Boson.zz (L : Multiset ℕ) = 0 := by exact_mod_cast h0
    rw [h1] at hd
    exact (Nat.factorial_pos h).ne' (Nat.eq_zero_of_zero_dvd hd)
  rw [bFam, op_smul_left, coef_smul, wt_ptn hL, hs, zz_eq, toN_ptn hL]
  have h2 : op (tpow (ptn L)) r (tpow σ) = opMon (toPNats L) r (tpow σ) := op_tpow (toPNats L) r (tpow σ)
  rw [h2, stBridge, toL_toPNats hL, ClauseBound.Boson.botK, Int.cast_mul, Int.cast_natCast, Nat.cast_div hd h0]
end GeneralPieces.Half
