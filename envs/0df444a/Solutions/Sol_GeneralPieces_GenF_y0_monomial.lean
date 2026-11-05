-- Prove2me | solution 1 for GeneralPieces.GenF.y0_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:02:36.262587+00:00
-- url     : https://prove2.me/submissions/06237be8-2052-4e34-9e82-a6180ed74659

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Theorems.Thm_GeneralPieces_GenF_y0_nil
import Theorems.Thm_GeneralPieces_GenF_y0_cons
import Theorems.Thm_GeneralPieces_GenF_JmU_monomial
import Theorems.Thm_GeneralPieces_GenF_CT_mul
import Theorems.Thm_ClauseBound_Boson_Basic_sum_erase_cast
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
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (a : List ℕ) : ∀ σ τ : Multiset ℕ, y0 a σ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) =
    C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum) := by
  induction a with
  | nil =>
    intro σ τ
    rw [y0_nil, MvPolynomial.coeff_monomial]
    by_cases h : σ = τ
    · subst h
      simp [op, one]
    · have h0 : op [] ((σ.sum : ℤ) - τ.sum) σ τ = 0 := by
        unfold op
        split_ifs <;> simp [one, h]
      rw [if_neg fun h' => h (Multiset.toFinsupp.injective h').symm, h0]
      simp
  | cons n a ih =>
    intro σ τ
    rw [y0_cons, JmU_monomial, map_sum]
    show _ = C ((nop n (op a) ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * _
    unfold nop
    rw [Int.cast_add, Int.cast_sum, Int.cast_sum, map_add, map_sum, map_sum, add_mul, sum_mul, sum_mul]
    have hs : (((n :: a).sum : ℕ) : ℤ) = (n : ℤ) + a.sum := by rw [List.sum_cons, Nat.cast_add]
    congr 1
    · refine sum_congr rfl fun l hl => ?_
      have hl' := Multiset.mem_toFinset.1 hl
      have e : (l : ℤ) - n + ((σ.sum : ℤ) - τ.sum - l - a.sum) = (σ.sum : ℤ) - τ.sum - ((n :: a).sum : ℕ) := by rw [hs]; ring
      rw [ih, Basic.sum_erase_cast hl', CT_mul, cre, if_pos hl', show (σ.sum : ℤ) - l - τ.sum = (σ.sum : ℤ) - τ.sum - l by ring, e, Int.cast_mul]
    · refine sum_congr rfl fun k hk => ?_
      have hk' := Multiset.mem_toFinset.1 hk
      have e : -(k : ℤ) - n + ((σ.sum : ℤ) - τ.sum + k - a.sum) = (σ.sum : ℤ) - τ.sum - ((n :: a).sum : ℕ) := by rw [hs]; ring
      have e2 : ((τ.count k : ℕ) : Lu) = C ((τ.count k : ℕ) : ℚ) := (map_natCast (C : ℚ →+* Lu) _).symm
      rw [map_smul, ih, Basic.sum_erase_cast hk', smul_eq_mul, e2, ← mul_assoc (C _) (C _) (T _), ← map_mul, CT_mul, ann,
        show (σ.sum : ℤ) - ((τ.sum : ℤ) - k) = (σ.sum : ℤ) - τ.sum + k by ring, e]
      congr 2
      push_cast
      ring
end GeneralPieces.GenF
