-- Prove2me | solution 1 for GlobalTheory.one_sub_re_pos_of_norm_le_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:14.138386+00:00
-- url     : https://prove2.me/submissions/055df1bb-7a73-485b-aea1-07eb831e6251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_OneSubRePosOfNormLeHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : 0 < (1 - z).re := by
  rw [Complex.sub_re, Complex.one_re]
  have := Complex.re_le_norm z
  linarith
end GlobalTheory
