-- Prove2me | solution 1 for GeneralPieces.Ring.pos_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:26:44.807247+00:00
-- url     : https://prove2.me/submissions/f1a9d3e4-0b35-4fba-bc80-756d906abe27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_pn_coe
import Theorems.Thm_GeneralPieces_Ring_nabla_pos_tpow
import Theorems.Thm_GeneralPieces_Ring_foldr_nabla_smul
import Theorems.Thm_GeneralPieces_Ring_nabla_foldr_pos
import Theorems.Thm_GeneralPieces_Ring_wt_erase

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (l : List ℤ) : (∀ x ∈ l, 0 < x) → ∀ σ : Ptn, (wt σ : ℤ) < l.sum → l.foldr nabla (tpow σ) = 0 := by
  induction l with
  | nil =>
    intro _ σ h
    simp at h
    omega
  | cons k l ih =>
    intro hl σ h
    have hk : 0 < k := hl k (by simp)
    have hl' : ∀ x ∈ l, 0 < x := fun x hx => hl x (by simp [hx])
    rw [List.foldr_cons, nabla_foldr_pos hk l hl', nabla_pos_tpow hk, foldr_nabla_smul]
    by_cases hm : pn k ∈ σ
    · rw [ih hl' (σ.erase (pn k)) ?_, smul_zero]
      have h1 := wt_erase hm
      have h2 := pn_coe hk.ne'
      rw [List.sum_cons] at h
      omega
    · rw [Multiset.count_eq_zero_of_notMem hm]
      simp
end GeneralPieces.Ring
