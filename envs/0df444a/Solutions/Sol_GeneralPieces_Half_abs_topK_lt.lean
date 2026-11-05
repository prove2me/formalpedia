-- Prove2me | solution 1 for GeneralPieces.Half.abs_topK_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:25.094001+00:00
-- url     : https://prove2.me/submissions/b64265a7-595d-4686-b386-1dfde0ea240a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_Half_Size
import Theorems.Thm_GeneralPieces_Half_factor_lt_big
import Theorems.Thm_GeneralPieces_Half_toN_ptn
import Theorems.Thm_GeneralPieces_Half_topK_eq
import Theorems.Thm_GeneralPieces_Half_wt_ptn
import Theorems.Thm_GeneralPieces_Sizes_abs_factor_a_le
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) {L : List ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (i : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : ClauseBound.Boson.Pos π)
    (hπ' : π.sum ≤ 4 * h) (hσ : ClauseBound.Boson.Pos σ) (hσ' : σ.sum ≤ 4 * h) : |ClauseBound.Boson.topK L h i r (π : Multiset ℕ) (σ : Multiset ℕ)| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := abs_factor_a_le hh i (ξ := ptn L) (by rw [wt_ptn hL, hs]) r (σ' := ptn π) (σ := ptn σ) (by rwa [wt_ptn hπ]) (by rwa [wt_ptn hσ])
  have h2 : |((ClauseBound.Boson.topK L h i r (π : Multiset ℕ) (σ : Multiset ℕ) : ℤ) : ℚ)| ≤ 2 ^ (3 * h) * 2 ^ (12 * h ^ 2) := by
    rw [← toN_ptn hπ, ← toN_ptn hσ, topK_eq hL hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact h1
  have h3 : |ClauseBound.Boson.topK L h i r (π : Multiset ℕ) (σ : Multiset ℕ)| ≤ ((2 ^ (3 * h) * 2 ^ (12 * h ^ 2) : ℕ) : ℤ) := by exact_mod_cast h2
  exact h3.trans_lt (by exact_mod_cast (factor_lt_big h).1)
end GeneralPieces.Half
