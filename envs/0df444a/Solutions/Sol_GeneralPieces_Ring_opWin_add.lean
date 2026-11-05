-- Prove2me | solution 1 for GeneralPieces.Ring.opWin_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:36:48.304761+00:00
-- url     : https://prove2.me/submissions/9931a9a4-b84a-4829-9d92-a540d0598791

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_term_add

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (M : ℕ) (r : ℤ) (f g : V) : opWin μ M r (f + g) = opWin μ M r f + opWin μ M r g := by
  unfold opWin
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ks _ => term_add μ ks f g
end GeneralPieces.Ring
