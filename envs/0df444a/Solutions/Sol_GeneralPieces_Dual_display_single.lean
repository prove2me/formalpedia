-- Prove2me | solution 1 for GeneralPieces.Dual.display_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:23:06.559249+00:00
-- url     : https://prove2.me/submissions/4acc3020-61ac-42a5-8e9e-78b802acacb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_mem_posTuples
import Theorems.Thm_GeneralPieces_Dual_display
import Theorems.Thm_GeneralPieces_Dual_le_of_prod_ne_zero
import Theorems.Thm_P2M_GeneralPieces_Dual_eq_of_forall__le_737cce703f30
import Theorems.Thm_GeneralPieces_Dual_sum_cast
import Theorems.Thm_GeneralPieces_Dual_prod_theta_self

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (h : ℕ) (μ : List ℕ+) (hμ : wt (μ : Multiset ℕ+) = h) (b : V) (hb : b ∈ VE h) :
    op (μ.map y).prod (-(h : ℤ)) b = (sgn μ : ℚ) • nablas (μ.map fun n : ℕ+ => (n : ℤ)) b := by
  rw [display h μ b hb, sum_eq_single (μ.map fun n : ℕ+ => (n : ℤ)), prod_theta_self]
  · intro ks hks hne
    obtain ⟨hl, hpos, hs⟩ := (mem_posTuples _ _ _).1 hks
    have h0 : (List.zipWith theta μ ks).prod = 0 := by
      by_contra hc
      exact hne (eq_of_forall₂_le μ ks (le_of_prod_ne_zero μ ks hl hpos hc) (by rw [hs, sum_cast, hμ]))
    rw [h0]; simp
  · intro hn
    exfalso
    apply hn
    rw [mem_posTuples]
    refine ⟨by simp, ?_, by rw [sum_cast, hμ]⟩
    intro k hk
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 hk
    exact_mod_cast n.pos
end GeneralPieces.Dual
