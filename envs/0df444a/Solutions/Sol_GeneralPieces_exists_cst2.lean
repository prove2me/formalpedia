-- Prove2me | solution 1 for GeneralPieces.exists_cst2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:45.350379+00:00
-- url     : https://prove2.me/submissions/6e6caf37-28cf-453d-b1d3-7d856e35a055

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_GeneralPieces_Half_Consts
import Theorems.Thm_GeneralPieces_Consts_numbers_of_thmHalfPieces
import Theorems.Thm_GeneralPieces_Consts_cap_le
import Theorems.Thm_GeneralPieces_Consts_pad_le
import Theorems.Thm_ClauseBound_Boson_Final_big_le
import Theorems.Thm_ClauseBound_Part_exists_bounds
import Theorems.Thm_GeneralPieces_Bits_exists_Delta_le
import Theorems.Thm_GeneralPieces_Bits_exists_hOf_le
import Theorems.Thm_GeneralPieces_Lex_hOf_eq
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Real ClauseBound.Inst.Half
open Consts
namespace GeneralPieces
theorem _root_.solution (hT : AppHalfPieces.ThmHalfPiecesPure) : ∃ c₀ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam := by
  obtain ⟨B, C, hB⟩ := ClauseBound.Part.exists_bounds
  obtain ⟨cT, hnum⟩ := numbers_of_thmHalfPieces hT
  obtain ⟨c₀, hh0⟩ := Bits.exists_hOf_le hB
  obtain ⟨c₂, hall⟩ := Bits.exists_Delta_le hB
  refine ⟨c₀, cT + (4 * c₀ + 2 * c₂ + 28) + 4 + (40 * (c₀ + 1) ^ 2 + c₂), fun lam hl => ?_⟩
  have hh := hh0 lam hl
  have hD : ∑ E ∈ range (4 * AppHalfPieces.hOf lam + 1), Partitions.p E ≤ 2 ^ (c₂ * lam) := hall lam hl
  obtain ⟨h1, h2, h3⟩ := hnum lam hl
  have hbig := ClauseBound.Boson.Final.big_le (c₁ := cT + (4 * c₀ + 2 * c₂ + 28)) hl hh hD
  have hpad := pad_le hl hh hD
  generalize hc : cT + (4 * c₀ + 2 * c₂ + 28) + 4 + (40 * (c₀ + 1) ^ 2 + c₂) = c at hbig ⊢
  rw [Lex.hOf_eq] at hh hD h1 h2 h3 hbig hpad
  have hpow : (2 * lam) ^ cT ≤ (2 * lam) ^ c := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨hh, h1.trans hpow, h2.trans_le (Nat.pow_le_pow_right (by norm_num) hpow), hbig,
    hpad.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))), fun s hs => ?_⟩
  have h4 := cap_le hl (h3 s hs)
  have h5 : (3 + cT) * lam ≤ 2 * c * lam := Nat.mul_le_mul_right _ (by omega)
  have hL : 0 ≤ logb 2 (2 * (lam : ℝ)) := Real.logb_nonneg one_lt_two (by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith)
  have h6 : (cT : ℝ) * logb 2 (2 * (lam : ℝ)) ≤ (c : ℝ) * logb 2 (2 * (lam : ℝ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : cT ≤ c)) hL
  exact ⟨(Nat.le_add_right _ _).trans (h4.trans h5), (Nat.le_add_left _ _).trans (h4.trans h5), (h3 s hs).trans (by linarith)⟩
end GeneralPieces
