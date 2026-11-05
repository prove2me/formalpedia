-- Prove2me | solution 1 for GeneralPieces.Ring.isInt_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:22:45.08922+00:00
-- url     : https://prove2.me/submissions/726ea71b-39c2-40a9-b4be-e3ae129a0afc

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
theorem _root_.solution {f : V} (hf : IsInt f) (z : ℤ) : IsInt ((z : ℚ) • f) := fun m => by
  obtain ⟨z', hz'⟩ := hf m
  exact ⟨z * z', by rw [coeff_smul, hz', smul_eq_mul]; push_cast; rfl⟩
end GeneralPieces.Ring
