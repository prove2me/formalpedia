-- Prove2me | solution 1 for GeneralPieces.Ring.isInt_nabla
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:40:20.623931+00:00
-- url     : https://prove2.me/submissions/5219f1b4-8fbb-41ad-bc21-e18290232667

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_isInt_zero
import Theorems.Thm_GeneralPieces_Ring_isInt_zsmul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f : V} (hf : IsInt f) (k : ℤ) : IsInt (nabla k f) := by
  unfold AppHalfPieces.nabla
  split_ifs
  · intro m
    rw [coeff_X_mul']
    split_ifs
    · exact hf _
    · exact ⟨0, by simp⟩
  · refine isInt_zsmul (fun m => ?_) k
    obtain ⟨z, hz⟩ := hf (m + Finsupp.single (pn k) 1)
    exact ⟨z * (m (pn k) + 1), by rw [coeff_pderiv, hz]; push_cast; rfl⟩
  · exact isInt_zero
end GeneralPieces.Ring
