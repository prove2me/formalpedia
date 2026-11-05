-- Prove2me | solution 1 for GeneralPieces.Series.pow_mul_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:06:59.153786+00:00
-- url     : https://prove2.me/submissions/142f8cfa-f28c-40c0-8386-f377550b9092

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Theorems.Thm_GeneralPieces_Series_pow_mul_term
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
theorem _root_.solution (φ : L →ₐ[ℚ] S) {e : S} (h : φ dW * e = 1) (H : ℕ) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) :
    φ dW ^ H * (l.map fun c => c.1 • (e ^ c.2.1 * φ c.2.2)).sum = φ (l.map fun c => c.1 • (dW ^ (H - c.2.1) * c.2.2)).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, mul_add, ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'), map_add,
      pow_mul_term h (hl c List.mem_cons_self), map_smul, map_mul, map_pow]
end GeneralPieces.Series
