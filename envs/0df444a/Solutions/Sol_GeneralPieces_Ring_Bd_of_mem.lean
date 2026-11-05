-- Prove2me | solution 1 for GeneralPieces.Ring.Bd_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:36:14.893583+00:00
-- url     : https://prove2.me/submissions/dbc849b5-b688-484d-be8e-812b4c66fad8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_mem_VE_iff


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f : V} {E : ℤ} (hf : f ∈ VE E) : Bd f E := fun μ hμ => ((mem_VE_iff E f).1 hf μ hμ).le
end GeneralPieces.Ring
