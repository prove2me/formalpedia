-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.F_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:38.695757+00:00
-- url     : https://prove2.me/submissions/cd31f306-ad30-4c70-8bfa-3c442cbe535f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_Expansion_coeff_F_P
import Theorems.Thm_GeneralPieces_Series_Expansion_coeff_F_of_ne
import Theorems.Thm_GeneralPieces_Series_Expansion_qP_eq_zero
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
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) :
    X.F = ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), (qP a b s π σ : ℚ) • W s (-s) := by
  ext ⟨x, y⟩
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [W, AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_single, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, Prod.mk.injEq]
  by_cases h : x + y = 0
  · obtain rfl : y = -x := by omega
    rw [X.coeff_F_P, sum_eq_single x]
    · simp
    · intro s _ hs
      rw [if_neg (fun g => hs g.1), mul_zero]
    · intro hx
      rw [X.qP_eq_zero hab (by rw [mem_Icc, not_and_or] at hx; rcases hx with g | g; exacts [lt_abs.2 (Or.inr (by omega)), lt_abs.2 (Or.inl (by omega))])]
      simp
  · rw [X.coeff_F_of_ne h]
    exact (sum_eq_zero fun s _ => by rw [if_neg (fun g => h (by omega)), mul_zero]).symm
end Expansion
end GeneralPieces.Series
