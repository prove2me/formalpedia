-- Prove2me | solution 1 for GlobalTheory.eulerTerm_norm_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:22.108441+00:00
-- url     : https://prove2.me/submissions/ea8becfb-cf4b-478e-96a6-c66ed58ab3b3

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
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  have hn0 : 0 < n := by omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  have : (0 : ℝ) ≤ (n : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc ‖c‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) := by gcongr
    _ = (n : ℝ) ^ (-s.re) := one_mul _
end GlobalTheory
