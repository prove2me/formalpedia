-- Prove2me | solution 1 for GeneralPieces.Series.terms_vac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:08:49.853127+00:00
-- url     : https://prove2.me/submissions/54f728c2-46a4-4a60-9562-89ad05561bde

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
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
namespace GeneralPieces.Series
theorem _root_.solution (φ : L →ₐ[ℚ] S) (e : S) (H : ℕ) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) (ht : ∀ c ∈ l, c.2.1 = H → c.2.2 = 1)
    (hv : ∀ c ∈ l, c.2.1 < H → c.2.2 = 0) :
    (l.map fun c => c.1 • (e ^ c.2.1 * φ c.2.2)).sum = ((l.filter fun c => c.2.1 = H).map fun c => c.1).sum • e ^ H := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) (fun c' hc' => ht c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hv c' (List.mem_cons_of_mem _ hc'))]
    by_cases h : c.2.1 = H
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ht c List.mem_cons_self h, h, map_one, mul_one, add_smul]
    · rw [List.filter_cons_of_neg (by simpa using h), hv c List.mem_cons_self (lt_of_le_of_ne (hl c List.mem_cons_self) h), map_zero, mul_zero, smul_zero, zero_add]
end GeneralPieces.Series
