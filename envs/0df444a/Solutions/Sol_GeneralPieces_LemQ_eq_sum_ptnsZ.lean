-- Prove2me | solution 1 for GeneralPieces.LemQ.eq_sum_ptnsZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:38:54.010892+00:00
-- url     : https://prove2.me/submissions/a29a4d55-d4db-43d3-a91c-3451d42a4efc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_eq_sum_of_subset
import Theorems.Thm_GeneralPieces_Ring_mem_VE_iff
import Theorems.Thm_GeneralPieces_Ring_mem_ptnsZ


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution {E : ℤ} {f : V} (hf : f ∈ VE E) : f = ∑ μ ∈ ptnsZ E, coef μ f • tpow μ :=
  eq_sum_of_subset f _ fun μ hμ => (mem_ptnsZ E μ).2 ((mem_VE_iff E f).1 hf μ hμ)
end GeneralPieces.LemQ
