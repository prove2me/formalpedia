-- Prove2me | solution 1 for GeneralPieces.Series.sum_qP_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:15:56.957428+00:00
-- url     : https://prove2.me/submissions/61f2695a-53be-4d4e-b881-fc828cc79e6f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Theorems.Thm_GeneralPieces_Series_Expansion_const
import Theorems.Thm_GeneralPieces_Series_Expansion_sum_qP
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
variable {A : FA} {b : List ℕ}
namespace GeneralPieces.Series
theorem _root_.solution (h : StExpansion) {a : List ℕ} (ha : Pos a) (hb : Pos b) (hab : a.sum ≤ b.sum) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), qP a b s π σ = if π = σ then op a (-(b.sum : ℤ)) 0 (b : Multiset ℕ) else 0 := by
  obtain ⟨G, hG⟩ := h a b ha hb
  obtain ⟨X⟩ := hG π σ hπ hσ
  obtain ⟨X0⟩ := hG 0 0 (by simp) (by simp)
  have h1 := X.sum_qP hab
  rw [X0.const hb] at h1
  exact_mod_cast h1
end GeneralPieces.Series
