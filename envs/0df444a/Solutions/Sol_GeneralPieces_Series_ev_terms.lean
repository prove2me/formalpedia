-- Prove2me | solution 1 for GeneralPieces.Series.ev_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:07:39.388788+00:00
-- url     : https://prove2.me/submissions/442c15f0-1221-4105-9fc2-01ddc36b4df7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Theorems.Thm_GeneralPieces_Series_ev_dW
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
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
theorem _root_.solution (H : ℕ) (v : L) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) (ht : ∀ c ∈ l, c.2.1 = H → c.2.2 = v) :
    ev (l.map fun c => c.1 • (dW ^ (H - c.2.1) * c.2.2)).sum = ((l.filter fun c => c.2.1 = H).map fun c => c.1).sum * ev v := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) (fun c' hc' => ht c' (List.mem_cons_of_mem _ hc')),
      map_smul, map_mul, map_pow, ev_dW]
    by_cases h : c.2.1 = H
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ht c List.mem_cons_self h, h, Nat.sub_self, pow_zero, one_mul, smul_eq_mul, add_mul]
    · have h2 := hl c List.mem_cons_self
      rw [List.filter_cons_of_neg (by simpa using h), zero_pow (by omega), zero_mul, smul_zero, zero_add]
end GeneralPieces.Series
