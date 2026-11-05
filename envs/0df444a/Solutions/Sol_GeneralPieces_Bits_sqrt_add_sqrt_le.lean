-- Prove2me | solution 1 for GeneralPieces.Bits.sqrt_add_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:31:34.536487+00:00
-- url     : https://prove2.me/submissions/6182dae9-eece-4ef8-8bf6-c75b968b6b48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}
namespace GeneralPieces.Bits
theorem _root_.solution {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) : √(2 * (h : ℝ) + s) + √(2 * (h : ℝ) - s) ≤ 2 * √(2 * (h : ℝ)) := by
  obtain ⟨a1, a2⟩ := abs_le.1 hs
  have b1 : -(2 * (h : ℝ)) ≤ s := by exact_mod_cast a1
  have b2 : (s : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast a2
  have e1 := Real.sq_sqrt (show 0 ≤ 2 * (h : ℝ) + s by linarith)
  have e2 := Real.sq_sqrt (show 0 ≤ 2 * (h : ℝ) - s by linarith)
  have e3 := Real.sq_sqrt (show 0 ≤ 2 * (h : ℝ) by positivity)
  have n1 := Real.sqrt_nonneg (2 * (h : ℝ) + s)
  have n2 := Real.sqrt_nonneg (2 * (h : ℝ) - s)
  have n3 := Real.sqrt_nonneg (2 * (h : ℝ))
  by_contra hc
  nlinarith [sq_nonneg (√(2 * (h : ℝ) + s) - √(2 * (h : ℝ) - s))]
end GeneralPieces.Bits
