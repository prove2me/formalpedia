-- Prove2me | solution 1 for GeneralPieces.Dual.sum_tuples_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:26:26.661195+00:00
-- url     : https://prove2.me/submissions/c2f8105c-32ad-4766-9a32-a2d1c0658749

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
namespace GeneralPieces.Dual
theorem _root_.solution {α M : Type} [DecidableEq α] [AddCommMonoid M] (s : Finset α) (r : List (Finset α)) (F : List α → M) :
    ∑ x ∈ tuples (s :: r), F x = ∑ a ∈ s, ∑ x ∈ tuples r, F (a :: x) := by
  rw [tuples, sum_image, sum_product]
  intro p _ q _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2
end GeneralPieces.Dual
