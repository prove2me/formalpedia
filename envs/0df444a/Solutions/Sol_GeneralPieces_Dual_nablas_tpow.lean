-- Prove2me | solution 1 for GeneralPieces.Dual.nablas_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:58.05723+00:00
-- url     : https://prove2.me/submissions/f644929d-bc81-4df3-96e7-176144fcf992

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_nablas_tpow_eq_zero
import Theorems.Thm_GeneralPieces_Dual_eq_of_count_le
import Theorems.Thm_GeneralPieces_Dual_nablas_tpow_self

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) (ν : Ptn) (hw : wt (μ : Multiset ℕ+) = wt ν) :
    nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow ν) = C (if (μ : Multiset ℕ+) = ν then (zz (μ : Multiset ℕ+) : ℚ) else 0) := by
  by_cases h : ∃ k, ν.count k < (μ : Multiset ℕ+).count k
  · obtain ⟨k, hk⟩ := h
    have hne : (μ : Multiset ℕ+) ≠ ν := fun he => by rw [he] at hk; omega
    rw [nablas_tpow_eq_zero μ ν k hk, if_neg hne, C_0]
  · have he : (μ : Multiset ℕ+) = ν := eq_of_count_le _ _ (fun k => not_lt.1 fun hk => h ⟨k, hk⟩) hw
    rw [if_pos he, ← he, nablas_tpow_self]
end GeneralPieces.Dual
