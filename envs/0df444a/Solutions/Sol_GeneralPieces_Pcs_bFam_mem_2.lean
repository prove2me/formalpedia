-- Prove2me | solution 2 for GeneralPieces.Pcs.bFam_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:46.726535+00:00
-- url     : https://prove2.me/submissions/7fdadf3d-1d5f-4614-a06f-15a6cce13692

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Ring_tpow_mem_VE


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (ν : Ptn) : bFam ν ∈ VE (wt ν : ℤ) := Submodule.smul_mem _ _ (tpow_mem_VE ν)
end GeneralPieces.Pcs
