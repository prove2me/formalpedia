-- Prove2me | solution 1 for GeneralPieces.Consts.cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:54.951741+00:00
-- url     : https://prove2.me/submissions/f298d049-b694-4234-a734-413096665592

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_GeneralPieces_Half_Consts
import Theorems.Thm_GeneralPieces_Consts_four_mul_rho_le
import Theorems.Thm_GeneralPieces_Bits_logb_two_mul_le


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Real ClauseBound.Inst.Half
open GeneralPieces.Consts
namespace GeneralPieces.Consts
theorem _root_.solution {a b c lam : ℕ} (hl : 1 ≤ lam) (h : ((a + b : ℕ) : ℝ) ≤ 4 * (1 / √2) * lam + c * logb 2 (2 * lam)) : a + b ≤ (3 + c) * lam := by
  have h1 : 4 * (1 / √(2 : ℝ)) * lam ≤ 3 * lam := mul_le_mul_of_nonneg_right four_mul_rho_le (Nat.cast_nonneg _)
  have h2 : (c : ℝ) * logb 2 (2 * lam) ≤ c * lam := mul_le_mul_of_nonneg_left (Bits.logb_two_mul_le hl) (Nat.cast_nonneg _)
  have h3 : ((a + b : ℕ) : ℝ) ≤ (((3 + c) * lam : ℕ) : ℝ) := by
    push_cast at h ⊢
    linarith
  exact_mod_cast h3
end GeneralPieces.Consts
