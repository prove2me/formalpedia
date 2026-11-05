-- Prove2me | solution 1 for GeneralPieces.Ring.sum_Pz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:27:40.668245+00:00
-- url     : https://prove2.me/submissions/300178f0-524b-4141-81dc-e8d89cac0895

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_Pz_eq
import Theorems.Thm_GeneralPieces_Ring_toN_injective


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {A : Type} [AddCommMonoid A] (m : ℤ) (G : Multiset ℕ → A) : ∑ τ ∈ ClauseBound.Boson.Pz m, G τ = ∑ τ ∈ ptnsZ m, G (toN τ) := by
  rw [Pz_eq, sum_image fun _ _ _ _ h => toN_injective h]
end GeneralPieces.Ring
