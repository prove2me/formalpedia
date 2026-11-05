-- Prove2me | solution 1 for GeneralPieces.GenF.JmT_JpV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:52:39.823791+00:00
-- url     : https://prove2.me/submissions/426f3c45-82ee-4dac-9418-e557aeb341d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Commute
import Theorems.Thm_GeneralPieces_GenF_JmU_C_mul_X
import Theorems.Thm_ClauseBound_Boson_Scalars_choose_eq_zero
import Theorems.Thm_GeneralPieces_Series_cfP_sumP
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X
namespace GeneralPieces.GenF
theorem _root_.solution (p q : ℕ) : JmT p (JpV q) = emb (kapS p q) := by
  refine HahnSeries.ext (funext fun y => ?_)
  show JmU p ((JpV q).coeff y) = MvPolynomial.C ((kapS p q).coeff y)
  rw [JpV, HahnSeries.coeff_ofSuppBddBelow]
  have hR : ∀ x : ℤ, ((kapS p q).coeff y).coeff x = cfP (kapS p q) x y := fun _ => rfl
  by_cases hy : 0 ≤ y
  · rw [if_pos hy, JmU_C_mul_X]
    congr 1
    ext x
    rw [hR, kapS, cfP_sumP, ← mul_assoc, ← map_mul, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    have hk : (((y + q).toNat : ℕ) : ℤ) = y + q := Int.toNat_of_nonneg (by omega)
    rw [hk]
    have hkq : (((y + q).toNat : ℕ) : ℚ) = (y : ℚ) + q := by exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hk
    rw [hkq]
    by_cases h0 : y + q = 0
    · have hb : bet q (y + q) = 0 := by rw [bet, if_pos h0]
      rw [hb, Int.cast_zero, zero_mul, ite_self, if_neg (by omega)]
    · by_cases hx : x + y = -((p : ℤ) + q)
      · rw [if_pos (by omega), if_pos ⟨by omega, hx⟩, bet, if_neg h0, bet, if_neg (by omega)]
        push_cast
        ring
      · rw [if_neg (by omega), if_neg (fun g => hx g.2)]
  · rw [if_neg hy, map_zero]
    symm
    rw [← map_zero (MvPolynomial.C : Lu →+* Vu)]
    congr 1
    ext x
    rw [hR, kapS, cfP_sumP]
    split_ifs with h
    · rw [Scalars.choose_eq_zero (r := y + q - 1) (k := q - 1) (by omega) (by omega)]
      simp
    · rfl
end GeneralPieces.GenF
