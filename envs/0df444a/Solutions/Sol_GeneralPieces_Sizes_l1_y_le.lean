-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_y_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:30:45.439131+00:00
-- url     : https://prove2.me/submissions/ffe8fef2-e084-417f-a45c-12526fdcb700

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

private theorem l1_eq_sum_aux {a : V} {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) :
    l1 a = ∑ m ∈ S, |coeff m a| :=
  sum_subset hS fun m _ hm => by rw [notMem_support_iff.1 hm, abs_zero]

private theorem l1_zero_aux : l1 (0 : V) = 0 := by simp [l1]

private theorem l1_add_le_aux (a b : V) : l1 (a + b) ≤ l1 a + l1 b := by
  classical
  rw [l1_eq_sum_aux (support_add (p := a) (q := b)),
    l1_eq_sum_aux (a := a) (subset_union_left (s₂ := b.support)),
    l1_eq_sum_aux (a := b) (subset_union_right (s₁ := a.support)), ← sum_add_distrib]
  exact sum_le_sum fun m _ => by rw [coeff_add]; exact abs_add_le _ _

private theorem l1_sum_le_aux {ι : Type} (s : Finset ι) (F : ι → V) :
    l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero_aux]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (l1_add_le_aux _ _).trans (by gcongr)

private theorem l1_smul_aux (q : ℚ) (a : V) : l1 (q • a) = |q| * l1 a := by
  rw [l1_eq_sum_aux (support_smul (a := q) (f := a)), l1, mul_sum]
  exact sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul, abs_mul]

private theorem l1_monomial_le_aux (m : ℕ+ →₀ ℕ) (q : ℚ) : l1 (monomial m q) ≤ |q| := by
  classical
  rw [l1_eq_sum_aux (support_monomial_subset (s := m) (a := q)), sum_singleton,
    coeff_monomial, if_pos rfl]

theorem solution (n : ℕ+) : l1 (y n) ≤ 2 ^ (n : ℕ) := by
  have a1 : ∑ j ∈ Icc 1 (n : ℕ), (n : ℕ).choose j ≤ 2 ^ (n : ℕ) := by
    rw [← Nat.sum_range_choose]
    exact sum_le_sum_of_subset fun j hj => mem_range.2 (by have := (mem_Icc.1 hj).2; omega)
  calc l1 (y n) ≤ ∑ j ∈ Icc 1 (n : ℕ), (((n : ℕ).choose j : ℕ) : ℚ) := by
        refine (l1_sum_le_aux _ _).trans (sum_le_sum fun j _ => ?_)
        rw [l1_smul_aux, Nat.abs_cast]
        have : l1 (X j.toPNat' : V) ≤ 1 := (l1_monomial_le_aux _ _).trans_eq abs_one
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) this
    _ ≤ 2 ^ (n : ℕ) := by exact_mod_cast a1
