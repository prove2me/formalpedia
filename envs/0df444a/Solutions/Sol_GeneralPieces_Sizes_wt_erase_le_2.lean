-- Prove2me | solution 2 for GeneralPieces.Sizes.wt_erase_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:31:53.514707+00:00
-- url     : https://prove2.me/submissions/5756fdef-8154-4db6-acff-5c619270e4be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem solution (σ : Ptn) (l : ℕ+) : wt (σ.erase l) ≤ wt σ := by
  by_cases h : l ∈ σ
  · have heq : (l : ℕ) + wt (σ.erase l) = wt σ := by
      simpa [wt] using congrArg wt (Multiset.cons_erase h)
    omega
  · rw [Multiset.erase_of_notMem h]
