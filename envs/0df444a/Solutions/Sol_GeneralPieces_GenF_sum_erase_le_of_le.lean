-- Prove2me | solution 1 for GeneralPieces.GenF.sum_erase_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:54:20.891321+00:00
-- url     : https://prove2.me/submissions/354c6537-3e2e-4f09-8cfb-15f04588e7c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution {σ : Multiset ℕ} {E : ℕ} (h : σ.sum ≤ E) (l : ℕ) : (σ.erase l).sum ≤ E := by
  by_cases hl : l ∈ σ
  · have := Multiset.sum_erase hl
    omega
  · rwa [Multiset.erase_of_notMem hl]
end GeneralPieces.GenF
