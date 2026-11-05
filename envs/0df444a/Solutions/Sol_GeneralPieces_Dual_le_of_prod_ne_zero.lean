-- Prove2me | solution 1 for GeneralPieces.Dual.le_of_prod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:18:41.309641+00:00
-- url     : https://prove2.me/submissions/0fc84561-e10c-4888-b0ad-6eac8b282ead

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_theta_of_lt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (hl : ks.length = μ.length) (hpos : ∀ k ∈ ks, 1 ≤ k)
    (h : (List.zipWith theta μ ks).prod ≠ 0) : List.Forall₂ (fun (n : ℕ+) (k : ℤ) => (n : ℤ) ≤ k) μ ks := by
  induction μ generalizing ks with
  | nil =>
    have : ks = [] := List.length_eq_zero_iff.1 hl
    subst this
    exact List.Forall₂.nil
  | cons n μ ih =>
    cases ks with
    | nil => simp at hl
    | cons k ks =>
      rw [List.zipWith_cons_cons, List.prod_cons] at h
      refine List.Forall₂.cons ?_ (ih ks (by simpa using hl) (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) (right_ne_zero_of_mul h))
      by_contra hc
      exact left_ne_zero_of_mul h (theta_of_lt n k (hpos k List.mem_cons_self) (by omega))
end GeneralPieces.Dual
