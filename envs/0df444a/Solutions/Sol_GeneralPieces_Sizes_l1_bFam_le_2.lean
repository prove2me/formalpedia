-- Prove2me | solution 2 for GeneralPieces.Sizes.l1_bFam_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:31:52.873908+00:00
-- url     : https://prove2.me/submissions/7920a750-873f-44f2-9a67-25ac80a1ed69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

private theorem l1_eq_sum_aux {a : V} {S : Finset (ℕ+ →₀ ℕ)}
    (hS : a.support ⊆ S) : l1 a = ∑ m ∈ S, |coeff m a| :=
  sum_subset hS fun m _ hm => by rw [notMem_support_iff.1 hm, abs_zero]

private theorem l1_smul_aux (q : ℚ) (a : V) : l1 (q • a) = |q| * l1 a := by
  rw [l1_eq_sum_aux (support_smul (a := q) (f := a)), l1, mul_sum]
  exact sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul, abs_mul]

private theorem l1_monomial_le_aux (m : ℕ+ →₀ ℕ) (q : ℚ) : l1 (monomial m q) ≤ |q| := by
  classical
  rw [l1_eq_sum_aux (support_monomial_subset (s := m) (a := q)),
    sum_singleton, coeff_monomial, if_pos rfl]

private theorem zz_pos_aux (μ : Ptn) : 0 < zz μ :=
  prod_pos fun k _ => Nat.mul_pos (pow_pos k.pos _) (Nat.factorial_pos _)

theorem solution (μ : Ptn) : l1 (bFam μ) ≤ (wt μ).factorial := by
  unfold bFam
  rw [l1_smul_aux]
  have a1 : l1 (tpow μ) ≤ 1 := (l1_monomial_le_aux _ _).trans_eq abs_one
  have a2 : (1 : ℚ) ≤ zz μ := by exact_mod_cast zz_pos_aux μ
  have a3 : |((wt μ).factorial : ℚ) / zz μ| ≤ (wt μ).factorial := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self (Nat.cast_nonneg _) a2
  calc _ ≤ ((wt μ).factorial : ℚ) * 1 := mul_le_mul a3 a1 (sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := mul_one _
