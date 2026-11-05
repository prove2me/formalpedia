-- Prove2me | solution 1 for GeneralPieces.Pcs.Le.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:39.90395+00:00
-- url     : https://prove2.me/submissions/568038cf-e18e-4492-b11d-5b2b4e1f4ee7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_Le_smul
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_GeneralPieces_Pcs_le_tpow
import Theorems.Thm_GeneralPieces_Pcs_tpow_mul
import Theorems.Thm_GeneralPieces_Pcs_wt_add
import Theorems.Thm_GeneralPieces_LemQ_Tri_smul
import Theorems.Thm_GeneralPieces_LemQ_eq_sum_of_subset
import Theorems.Thm_GeneralPieces_LemQ_mem_ptnsLe


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
namespace Le
theorem _root_.solution {h h' : ℕ} {a a' : V} (ha : Le h a) (ha' : Le h' a') : Le (h + h') (a * a') := by
  rw [eq_sum_of_subset a (ptnsLe h) fun μ hμ => (mem_ptnsLe h μ).2 (ha μ hμ), eq_sum_of_subset a' (ptnsLe h') fun μ hμ => (mem_ptnsLe h' μ).2 (ha' μ hμ), sum_mul_sum]
  refine Le.sum _ fun μ hμ => Le.sum _ fun ν hν => ?_
  rw [smul_mul_smul_comm, tpow_mul]
  refine (le_tpow ?_).smul _
  rw [wt_add]
  exact Nat.add_le_add ((mem_ptnsLe h μ).1 hμ) ((mem_ptnsLe h' ν).1 hν)
end Le
end GeneralPieces.Pcs
