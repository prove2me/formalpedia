-- Prove2me | solution 1 for GeneralPieces.GenF.sum_erase_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:02:07.460932+00:00
-- url     : https://prove2.me/submissions/e716afe6-4195-4196-8e80-7c27c4f069f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
namespace GeneralPieces.GenF
theorem _root_.solution (σ : Multiset ℕ) (l : ℕ) : (σ.erase l).sum ≤ σ.sum := by
  by_cases h : l ∈ σ
  · have := Multiset.sum_erase h
    omega
  · rw [Multiset.erase_of_notMem h]
end GeneralPieces.GenF
