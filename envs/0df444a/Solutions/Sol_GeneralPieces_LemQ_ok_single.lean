-- Prove2me | solution 1 for GeneralPieces.LemQ.ok_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:58.241202+00:00
-- url     : https://prove2.me/submissions/15374c2e-2be2-4059-93d6-acda68fbb1b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_sum_lst
import Theorems.Thm_GeneralPieces_LemQ_pos_lst

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution {h : ℕ} {μ ν : Ptn} (hμ : wt μ ≤ h) (hν : wt ν = h) : ClauseBound.Boson.FA.Ok [((1 : ℤ), lst μ)] (lst ν).sum := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact ⟨pos_lst μ, by rw [sum_lst, sum_lst, hν]; exact hμ⟩
end GeneralPieces.LemQ
