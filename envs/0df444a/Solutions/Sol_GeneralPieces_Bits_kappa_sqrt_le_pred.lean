-- Prove2me | solution 1 for GeneralPieces.Bits.kappa_sqrt_le_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:57.554601+00:00
-- url     : https://prove2.me/submissions/5bf156fb-fd5e-439b-8c33-f0c7a0256718

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_ClauseBound_Part_Bits_kappa_pos


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) : kappa * √(h : ℝ) ≤ kappa * √((h : ℝ) - 1) + kappa := by
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h9 : √(h : ℝ) ≤ √((h : ℝ) - 1) + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h10 := Real.sq_sqrt (show 0 ≤ (h : ℝ) - 1 by linarith)
    have h11 := Real.sqrt_nonneg ((h : ℝ) - 1)
    nlinarith
  have := mul_le_mul_of_nonneg_left h9 ClauseBound.Part.Bits.kappa_pos.le
  linarith
end GeneralPieces.Bits
