-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:18.253239+00:00
-- url     : https://prove2.me/submissions/623d9bd7-d77d-451e-8704-cee20f261c16

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution {a : V} (ha : IsInt a) (h' : ℕ) : IsInt (part h' a) := fun m => by
  classical
  unfold part
  rw [coeff_weightedHomogeneousComponent]
  split_ifs
  · exact ha m
  · exact ⟨0, by simp⟩
end GeneralPieces.Pcs
