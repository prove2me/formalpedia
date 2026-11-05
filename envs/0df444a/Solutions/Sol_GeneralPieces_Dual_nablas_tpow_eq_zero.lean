-- Prove2me | solution 1 for GeneralPieces.Dual.nablas_tpow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:42.410265+00:00
-- url     : https://prove2.me/submissions/f3ffd7ae-d7ce-4fbd-b428-019e91e7b87e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_nablas_snoc_tpow
import Theorems.Thm_GeneralPieces_Dual_coe_snoc

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) (ν : Ptn) (k : ℕ+) (h : ν.count k < (μ : Multiset ℕ+).count k) :
    nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow ν) = 0 := by
  induction μ using List.reverseRecOn generalizing ν with
  | nil => simp at h
  | append_singleton μ n ih =>
    rw [nablas_snoc_tpow]
    by_cases hn : n ∈ ν
    · rw [ih (ν.erase n) ?_, smul_zero]
      rw [coe_snoc, Multiset.count_cons] at h
      by_cases hkn : k = n
      · subst hkn
        have := Multiset.count_pos.2 hn
        rw [Multiset.count_erase_self]
        simp only [if_true] at h
        omega
      · rw [Multiset.count_erase_of_ne hkn]
        simpa [hkn] using h
    · rw [Multiset.count_eq_zero_of_notMem hn]; simp
end GeneralPieces.Dual
