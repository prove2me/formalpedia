-- Prove2me | solution 1 for GeneralPieces.Ring.exists_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:19:08.950823+00:00
-- url     : https://prove2.me/submissions/eca1e1be-43a3-49d5-97f8-b82cfbfa6e9e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_exists_Bd

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (f : V) (r : ℤ) : ∃ (E : ℤ) (M : ℕ), Bd f E ∧ E ≤ M ∧ E + r ≤ M := by
  obtain ⟨E, hE⟩ := exists_Bd f
  exact ⟨E, E + r.natAbs, hE, by omega, by omega⟩
end GeneralPieces.Ring
