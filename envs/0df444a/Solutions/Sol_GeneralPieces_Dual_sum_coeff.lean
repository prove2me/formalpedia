-- Prove2me | solution 1 for GeneralPieces.Dual.sum_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:19:20.273407+00:00
-- url     : https://prove2.me/submissions/a9f9d352-5c5b-4691-846b-fb26af5b585c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_sum_tuples_cons
import Theorems.Thm_GeneralPieces_Dual_binom_symm

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (hl : ks.length = μ.length) :
    ∑ js ∈ tuples (μ.map fun n : ℕ+ => Icc 1 (n : ℕ)), (List.zipWith (fun (n : ℕ+) (j : ℕ) => ((n : ℕ).choose j : ℚ)) μ js).prod *
      (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) (js.map Nat.toPNat') ks).prod : ℤ) : ℚ) =
    (((List.zipWith theta μ ks).prod : ℤ) : ℚ) := by
  induction μ generalizing ks with
  | nil => simp [tuples]
  | cons n μ ih =>
    cases ks with
    | nil => simp at hl
    | cons k ks =>
      rw [List.map_cons, sum_tuples_cons]
      simp only [List.zipWith_cons_cons, List.map_cons, List.prod_cons]
      rw [Int.cast_mul, ← ih ks (by simpa using hl), theta, Int.cast_sum, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [mul_sum]
      refine sum_congr rfl fun js _ => ?_
      obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
      have e1 : ((j.toPNat' : ℕ+) : ℤ) = j := by
        have : ((j.toPNat' : ℕ+) : ℕ) = j := by rw [Nat.toPNat'_coe, if_pos (by omega)]
        exact_mod_cast this
      rw [e1, binom_symm _ _ hj2]
      push_cast
      ring
end GeneralPieces.Dual
