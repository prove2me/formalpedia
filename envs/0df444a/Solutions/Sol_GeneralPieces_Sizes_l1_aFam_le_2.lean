-- Prove2me | solution 2 for GeneralPieces.Sizes.l1_aFam_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:33:46.513532+00:00
-- url     : https://prove2.me/submissions/604195a5-bfd3-4daf-b361-f0bb94e80811

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Sizes_l1_eq_sum
import Theorems.Thm_GeneralPieces_Sizes_l1_zero
import Theorems.Thm_GeneralPieces_Sizes_l1_add_le
import Theorems.Thm_GeneralPieces_Sizes_l1_nonneg
import Theorems.Thm_GeneralPieces_Sizes_l1_smul
import Theorems.Thm_GeneralPieces_Sizes_l1_monomial_le
import Theorems.Thm_GeneralPieces_Sizes_l1_y_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

private theorem l1_sum_le_aux {ι : Type} (s : Finset ι) (F : ι → V) :
    l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (l1_add_le _ _).trans (by gcongr)

private theorem l1_mul_le_aux (a b : V) : l1 (a * b) ≤ l1 a * l1 b := by
  have e : a * b = ∑ m ∈ a.support, ∑ m' ∈ b.support,
      monomial (m + m') (coeff m a * coeff m' b) := by
    conv_lhs => rw [← support_sum_monomial_coeff a, ← support_sum_monomial_coeff b]
    rw [sum_mul_sum]
    simp_rw [monomial_mul]
  calc
    l1 (a * b) ≤ ∑ m ∈ a.support, ∑ m' ∈ b.support, |coeff m a| * |coeff m' b| := by
      rw [e]
      exact (l1_sum_le_aux _ _).trans (sum_le_sum fun m _ =>
        (l1_sum_le_aux _ _).trans (sum_le_sum fun m' _ =>
          (l1_monomial_le _ _).trans_eq (abs_mul _ _)))
    _ = l1 a * l1 b := by rw [l1, l1, sum_mul_sum]

theorem solution (μ : Ptn) : l1 (aFam μ) ≤ 2 ^ wt μ := by
  induction μ using Multiset.induction_on with
  | empty =>
    have : aFam 0 = monomial 0 1 := by simp [aFam]
    rw [this]
    exact (l1_monomial_le _ _).trans (by simp [wt])
  | cons n μ ih =>
    have hw : wt (n ::ₘ μ) = n + wt μ := by
      unfold wt
      rw [Multiset.map_cons, Multiset.sum_cons]
    have e : aFam (n ::ₘ μ) = ((-1 : ℚ) ^ ((n : ℕ) - 1) • y n) * aFam μ := by
      unfold aFam
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [e, hw, pow_add]
    refine (l1_mul_le_aux _ _).trans (mul_le_mul ?_ ih (l1_nonneg _) (by positivity))
    rw [l1_smul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact l1_y_le n
