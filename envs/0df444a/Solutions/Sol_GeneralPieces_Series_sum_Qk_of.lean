-- Prove2me | solution 1 for GeneralPieces.Series.sum_Qk_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:17:25.762539+00:00
-- url     : https://prove2.me/submissions/fd7f9cb8-7656-4424-bb08-76185c3f1314

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Theorems.Thm_GeneralPieces_Series_sum_list_comm
import Theorems.Thm_GeneralPieces_Series_Qk_eq_sum
import Theorems.Thm_GeneralPieces_Series_sum_qP_of
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
theorem _root_.solution (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) :
    ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), Qk A b s π σ = if π = σ then pairF A b else 0 := by
  simp only [Qk_eq_sum hA]
  rw [sum_list_comm]
  have h1 : (A.map fun c => ∑ s ∈ Icc (-((σ.sum : ℤ) + b.sum)) ((σ.sum : ℤ) + b.sum), c.1 * qP c.2 b s π σ)
      = A.map fun c => c.1 * if π = σ then op c.2 (-(b.sum : ℤ)) 0 (b : Multiset ℕ) else 0 :=
    List.map_congr_left fun c hc => by rw [← mul_sum, sum_qP_of h (hA c hc).1 hb (hA c hc).2 hπ hσ]
  rw [h1]
  by_cases hπσ : π = σ
  · simp only [if_pos hπσ, pairF]
  · simp only [if_neg hπσ, mul_zero, List.map_const', List.sum_replicate, smul_zero]
end GeneralPieces.Series
