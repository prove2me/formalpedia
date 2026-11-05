-- Prove2me | solution 1 for GeneralPieces.Ring.opWin_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:03.720031+00:00
-- url     : https://prove2.me/submissions/4e27a968-6e8c-478d-9d53-a039d2ff41cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_term_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (M : ℕ) (r : ℤ) (q : ℚ) (f : V) : opWin μ M r (q • f) = q • opWin μ M r f := by
  unfold opWin
  rw [smul_sum]
  exact sum_congr rfl fun ks _ => term_smul μ ks q f
end GeneralPieces.Ring
