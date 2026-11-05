-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:25:37.772025+00:00
-- url     : https://prove2.me/submissions/7effde9b-3fee-472d-b4e5-8a6b319c1524

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
theorem _root_.solution {f g : V} (hf : IsInt f) (hg : IsInt g) : IsInt (f + g) := fun m => by
  obtain ⟨z, hz⟩ := hf m
  obtain ⟨w, hw⟩ := hg m
  exact ⟨z + w, by rw [coeff_add, hz, hw]; push_cast; rfl⟩
end GeneralPieces.Pcs
