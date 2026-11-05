-- Prove2me | solution 1 for GeneralPieces.Ring.isInt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:40:08.995056+00:00
-- url     : https://prove2.me/submissions/e12f9ebe-39d5-4903-bc17-0a545150c872

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f g : V} (hf : IsInt f) (hg : IsInt g) : IsInt (f + g) := fun m => by
  obtain ⟨z, hz⟩ := hf m
  obtain ⟨z', hz'⟩ := hg m
  exact ⟨z + z', by rw [coeff_add, hz, hz']; push_cast; rfl⟩
end GeneralPieces.Ring
