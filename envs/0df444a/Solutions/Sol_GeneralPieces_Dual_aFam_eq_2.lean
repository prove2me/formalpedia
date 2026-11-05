-- Prove2me | solution 2 for GeneralPieces.Dual.aFam_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:46:00.814809+00:00
-- url     : https://prove2.me/submissions/98eafc81-08e2-4f7c-8680-461cdbc5101a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem solution (μ : List ℕ+) : aFam (μ : Multiset ℕ+) = (sgn μ : ℚ) • (μ.map y).prod := by
  unfold aFam
  rw [Multiset.map_coe, Multiset.prod_coe]
  induction μ with
  | nil => simp [sgn]
  | cons n μ ih =>
    have h1 : sgn (n :: μ) = (-1 : ℤ) ^ ((n : ℕ) - 1) * sgn μ := by simp [sgn]
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, smul_mul_smul_comm, h1]
    push_cast
    rfl
