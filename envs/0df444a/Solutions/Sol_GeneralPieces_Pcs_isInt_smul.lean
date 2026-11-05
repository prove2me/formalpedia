-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:35.714178+00:00
-- url     : https://prove2.me/submissions/b64c85b9-8593-4bda-942f-82b8e51b8730

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
theorem _root_.solution {f : V} (hf : IsInt f) (z : ℤ) : IsInt ((z : ℚ) • f) := fun m => by
  obtain ⟨w, hw⟩ := hf m
  exact ⟨z * w, by rw [coeff_smul, hw, smul_eq_mul]; push_cast; rfl⟩
end GeneralPieces.Pcs
