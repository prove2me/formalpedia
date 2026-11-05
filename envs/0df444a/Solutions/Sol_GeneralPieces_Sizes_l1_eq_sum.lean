-- Prove2me | solution 1 for GeneralPieces.Sizes.l1_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:23:11.68948+00:00
-- url     : https://prove2.me/submissions/7927dcb7-8ecf-421d-8c33-2e9e076f24c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {a : V} {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) : l1 a = ∑ m ∈ S, |coeff m a| :=
  sum_subset hS fun m _ hm => by rw [notMem_support_iff.1 hm, abs_zero]
end GeneralPieces.Sizes
