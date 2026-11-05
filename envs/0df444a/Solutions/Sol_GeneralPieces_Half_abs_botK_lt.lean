-- Prove2me | solution 1 for GeneralPieces.Half.abs_botK_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:26.140898+00:00
-- url     : https://prove2.me/submissions/9b1a1f80-0d95-4118-b337-374244bf9940

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_Half_Size
import Theorems.Thm_GeneralPieces_Half_factor_lt_big
import Theorems.Thm_GeneralPieces_Half_botK_eq
import Theorems.Thm_GeneralPieces_Half_toN_ptn
import Theorems.Thm_GeneralPieces_Half_wt_ptn
import Theorems.Thm_GeneralPieces_Sizes_abs_factor_b_le
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half
namespace GeneralPieces.Half
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) {L : List ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (r : ℤ) {π σ : List ℕ} (hπ : ClauseBound.Boson.Pos π)
    (hπ' : π.sum ≤ 4 * h) (hσ : ClauseBound.Boson.Pos σ) (hσ' : σ.sum ≤ 4 * h) : |ClauseBound.Boson.botK L h r (π : Multiset ℕ) (σ : Multiset ℕ)| < 2 ^ ClauseBound.Boson.big h := by
  have h1 := abs_factor_b_le hh (ν := ptn L) (by rw [wt_ptn hL, hs]) r (σ' := ptn π) (σ := ptn σ) (by rwa [wt_ptn hπ]) (by rwa [wt_ptn hσ])
  have h2 : |((ClauseBound.Boson.botK L h r (π : Multiset ℕ) (σ : Multiset ℕ) : ℤ) : ℚ)| ≤ h.factorial * 2 ^ (12 * h ^ 2) := by
    rw [← toN_ptn hπ, ← toN_ptn hσ, botK_eq hL hs]
    exact h1
  have h3 : |ClauseBound.Boson.botK L h r (π : Multiset ℕ) (σ : Multiset ℕ)| ≤ ((h.factorial * 2 ^ (12 * h ^ 2) : ℕ) : ℤ) := by exact_mod_cast h2
  exact h3.trans_lt (by exact_mod_cast (factor_lt_big h).2)
end GeneralPieces.Half
