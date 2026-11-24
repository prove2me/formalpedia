-- Prove2me | solution 1 for GlobalTheory.eulerTerm_norm_le_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:01.454066+00:00
-- url     : https://prove2.me/submissions/f44df6d3-f93c-4478-b7e0-4efb36e38b66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_OneSubRePosOfNormLeHalf
import Theorems.Thm_GlobalTheory_eulerTerm_norm_le_rpow

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
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 1 < s.re) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  refine (eulerTerm_norm_le_rpow n hn c s hc).trans ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
end GlobalTheory
