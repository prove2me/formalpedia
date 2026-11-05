-- Prove2me | solution 1 for GeneralPieces.Pcs.Le.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:57.62733+00:00
-- url     : https://prove2.me/submissions/35fdf733-627d-4935-9ac2-27647a3833d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
namespace Le
theorem _root_.solution {h : ℕ} {a : V} (ha : Le h a) (q : ℚ) : Le h (q • a) := fun π hπ => ha π (by rw [coef_smul] at hπ; exact right_ne_zero_of_mul hπ)
end Le
end GeneralPieces.Pcs
