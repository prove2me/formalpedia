-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_bFam
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:08:16.348076+00:00
-- url     : https://prove2.me/submissions/28e72cbb-8700-4796-b226-686d5767f3f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem solution (hZ : ZDvd) (ν : Ptn) : IsInt (bFam ν) := by
  have isInt_smul {f : V} (hf : IsInt f) (z : ℤ) : IsInt ((z : ℚ) • f) := fun m => by
    obtain ⟨w, hw⟩ := hf m
    exact ⟨z * w, by rw [coeff_smul, hw, smul_eq_mul]; push_cast; rfl⟩
  have isInt_tpow (μ : Ptn) : IsInt (tpow μ) := fun m => by
    classical
    unfold tpow
    rw [coeff_monomial]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  unfold bFam
  have h0 : (zz ν : ℚ) ≠ 0 := by
    have : zz ν ≠ 0 := by
      unfold zz
      exact Finset.prod_ne_zero_iff.2 fun k _ =>
        Nat.mul_ne_zero (pow_ne_zero _ k.pos.ne') (Nat.factorial_ne_zero _)
    exact_mod_cast this
  have := isInt_smul (isInt_tpow ν) (((wt ν).factorial / zz ν : ℕ) : ℤ)
  rwa [Int.cast_natCast, Nat.cast_div (hZ ν) h0] at this
