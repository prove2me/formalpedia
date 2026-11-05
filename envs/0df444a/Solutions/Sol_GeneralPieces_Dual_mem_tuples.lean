-- Prove2me | solution 1 for GeneralPieces.Dual.mem_tuples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:24:25.105255+00:00
-- url     : https://prove2.me/submissions/a5e21f70-a274-45e5-ae59-78e1d9f9c3fd

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
theorem _root_.solution {α : Type} [DecidableEq α] (L : List (Finset α)) (x : List α) : x ∈ tuples L ↔ List.Forall₂ (fun a s => a ∈ s) x L := by
  induction L generalizing x with
  | nil => simp [tuples]
  | cons s r ih =>
    simp only [tuples, mem_image, mem_product, Prod.exists]
    constructor
    · rintro ⟨a, y, ⟨ha, hy⟩, rfl⟩
      exact List.Forall₂.cons ha ((ih y).1 hy)
    · intro h
      cases h with
      | cons ha hy => exact ⟨_, _, ⟨ha, (ih _).2 hy⟩, rfl⟩
end GeneralPieces.Dual
