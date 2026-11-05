-- Prove2me | solution 1 for GeneralPieces.Dual.prod_zip_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:17:35.730829+00:00
-- url     : https://prove2.me/submissions/329e3235-2eb0-4319-863c-55db13cbea19

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_tpow_cons

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (c : ℕ+ → ℕ → ℚ) (g : ℕ → ℕ+) (μ : List ℕ+) (js : List ℕ) (hl : js.length = μ.length) :
    (List.zipWith (fun n j => c n j • (X (g j) : V)) μ js).prod = (List.zipWith c μ js).prod • tpow ((js.map g : List ℕ+) : Multiset ℕ+) := by
  induction μ generalizing js with
  | nil =>
    have : js = [] := List.length_eq_zero_iff.1 hl
    subst this
    simp [tpow]
  | cons n μ ih =>
    cases js with
    | nil => simp at hl
    | cons j js =>
      simp only [List.zipWith_cons_cons, List.prod_cons, List.map_cons]
      rw [ih js (by simpa using hl), smul_mul_smul_comm, tpow_cons]
end GeneralPieces.Dual
