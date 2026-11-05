-- Prove2me | solution 2 for GeneralPieces.Dual.lemmaDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:28:13.084072+00:00
-- url     : https://prove2.me/submissions/346acef1-0f09-4afe-b92e-8344020e3d89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_aFam_op
import Theorems.Thm_GeneralPieces_Dual_nablas_smul
import Theorems.Thm_GeneralPieces_Dual_nablas_tpow
import Theorems.Thm_GeneralPieces_Dual_tpow_mem
import Theorems.Thm_GeneralPieces_Dual_zz_pos

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution : LemmaDual := by
  intro h μ ν hμ hν
  obtain ⟨l, rfl⟩ : ∃ l : List ℕ+, (l : Multiset ℕ+) = μ := ⟨μ.toList, Multiset.coe_toList μ⟩
  have hb : bFam ν ∈ VE h := by rw [← hν]; exact Submodule.smul_mem _ _ (tpow_mem ν)
  rw [aFam_op h l hμ _ hb, bFam, nablas_smul, nablas_tpow l ν (by rw [hμ, hν]), smul_eq_C_mul, ← C_mul]
  congr 1
  split_ifs with he
  · rw [← he, hμ]
    exact div_mul_cancel₀ _ (by exact_mod_cast (zz_pos _).ne')
  · simp
end GeneralPieces.Dual
