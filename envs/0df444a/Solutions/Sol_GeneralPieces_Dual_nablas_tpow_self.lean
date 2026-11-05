-- Prove2me | solution 1 for GeneralPieces.Dual.nablas_tpow_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:43.486065+00:00
-- url     : https://prove2.me/submissions/205e6ab9-e06e-4d8a-b154-b50ed82637d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_nablas_snoc_tpow
import Theorems.Thm_GeneralPieces_Dual_coe_snoc
import Theorems.Thm_GeneralPieces_Dual_zz_erase

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) : nablas (μ.map fun n : ℕ+ => (n : ℤ)) (tpow (μ : Multiset ℕ+)) = C (zz (μ : Multiset ℕ+) : ℚ) := by
  induction μ using List.reverseRecOn with
  | nil => simp [nablas, tpow, zz]
  | append_singleton μ n ih =>
    rw [nablas_snoc_tpow, coe_snoc, Multiset.erase_cons_head, ih, zz_erase (Multiset.mem_cons_self n _), Multiset.erase_cons_head,
      smul_eq_C_mul, ← C_mul]
    push_cast
    rfl
end GeneralPieces.Dual
