-- Prove2me | solution 1 for GeneralPieces.Sizes.card_terms_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:28:50.518868+00:00
-- url     : https://prove2.me/submissions/21a087df-eef8-4c25-a138-5ea4df667ba4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_card_le_wt
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) : #σ'.toFinset + #σ.toFinset ≤ 8 * h := by
  have a1 := (Multiset.toFinset_card_le σ').trans (card_le_wt σ')
  have a2 := (Multiset.toFinset_card_le σ).trans (card_le_wt σ)
  omega
end GeneralPieces.Sizes
