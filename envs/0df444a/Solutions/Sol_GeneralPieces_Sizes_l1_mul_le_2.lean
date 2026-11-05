-- Prove2me | solution 2 for GeneralPieces.Sizes.l1_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:32:11.774237+00:00
-- url     : https://prove2.me/submissions/882045f2-577a-4b5c-a2a9-6dc94ea1f6e3

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

theorem solution (a b : V) : l1 (a * b) ≤ l1 a * l1 b := by
  classical
  have l1_eq_sum {a : V} {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) :
      l1 a = ∑ m ∈ S, |coeff m a| :=
    sum_subset hS fun m _ hm => by rw [notMem_support_iff.1 hm, abs_zero]
  have l1_zero : l1 0 = 0 := by simp [l1]
  have l1_add_le (a b : V) : l1 (a + b) ≤ l1 a + l1 b := by
    rw [l1_eq_sum (support_add (p := a) (q := b)),
      l1_eq_sum (a := a) (subset_union_left (s₂ := b.support)),
      l1_eq_sum (a := b) (subset_union_right (s₁ := a.support)), ← sum_add_distrib]
    exact sum_le_sum fun m _ => by rw [coeff_add]; exact abs_add_le _ _
  have l1_sum_le {ι : Type} (s : Finset ι) (F : ι → V) :
      l1 (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1 (F i) := by
    induction s using Finset.induction_on with
    | empty => simp [l1_zero]
    | insert i s hi ih =>
      rw [sum_insert hi, sum_insert hi]
      exact (l1_add_le _ _).trans (by gcongr)
  have l1_monomial_le (m : ℕ+ →₀ ℕ) (q : ℚ) : l1 (monomial m q) ≤ |q| := by
    rw [l1_eq_sum (support_monomial_subset (s := m) (a := q)), sum_singleton,
      coeff_monomial, if_pos rfl]
  have e : a * b = ∑ m ∈ a.support, ∑ m' ∈ b.support,
      monomial (m + m') (coeff m a * coeff m' b) := by
    conv_lhs => rw [← support_sum_monomial_coeff a, ← support_sum_monomial_coeff b]
    rw [sum_mul_sum]
    simp_rw [monomial_mul]
  calc
    l1 (a * b) ≤ ∑ m ∈ a.support, ∑ m' ∈ b.support,
        |coeff m a| * |coeff m' b| := by
      rw [e]
      exact (l1_sum_le _ _).trans (sum_le_sum fun m _ =>
        (l1_sum_le _ _).trans (sum_le_sum fun m' _ =>
          (l1_monomial_le _ _).trans_eq (abs_mul _ _)))
    _ = l1 a * l1 b := by rw [l1, l1, sum_mul_sum]
