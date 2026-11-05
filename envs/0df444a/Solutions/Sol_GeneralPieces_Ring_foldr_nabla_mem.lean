-- Prove2me | solution 1 for GeneralPieces.Ring.foldr_nabla_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:38:29.680384+00:00
-- url     : https://prove2.me/submissions/d18258f3-6343-4dd8-ad38-e12290ef259a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_nabla_mem


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (l : List ℤ) (hl : ∀ k ∈ l, k ≠ 0) {E : ℤ} {f : V} (hf : f ∈ VE E) : l.foldr nabla f ∈ VE (E - l.sum) := by
  induction l with
  | nil => simpa using hf
  | cons k l ih =>
    rw [List.foldr_cons, List.sum_cons]
    have := nabla_mem (hl k (by simp)) (ih fun x hx => hl x (by simp [hx]))
    rwa [show E - l.sum - k = E - (k + l.sum) by ring] at this
end GeneralPieces.Ring
