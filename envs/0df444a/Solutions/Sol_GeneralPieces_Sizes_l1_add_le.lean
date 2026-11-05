-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_add_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:08:15.876022+00:00
-- url     : https://prove2.me/submissions/398bf69a-bc2d-4cc6-adfd-d2f6024638a9

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

private theorem l1_eq_sum_aux {a : V} {S : Finset (ℕ+ →₀ ℕ)}
    (hS : a.support ⊆ S) : l1 a = ∑ m ∈ S, |coeff m a| :=
  sum_subset hS fun m _ hm => by rw [notMem_support_iff.1 hm, abs_zero]

theorem solution (a b : V) : l1 (a + b) ≤ l1 a + l1 b := by
  classical
  rw [l1_eq_sum_aux (support_add (p := a) (q := b)),
    l1_eq_sum_aux (a := a) (subset_union_left (s₂ := b.support)),
    l1_eq_sum_aux (a := b) (subset_union_right (s₁ := a.support)), ← sum_add_distrib]
  exact sum_le_sum fun m _ => by rw [coeff_add]; exact abs_add_le _ _
