-- Prove2me | solution 1 for GeneralPieces.Pcs.isInt_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:30:36.962249+00:00
-- url     : https://prove2.me/submissions/fb1135e2-1ba0-4b3e-8172-7b8570e82d56

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
theorem _root_.solution (μ : Ptn) : IsInt (tpow μ) := fun m => by
  classical
  unfold tpow
  rw [coeff_monomial]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩
end GeneralPieces.Pcs
