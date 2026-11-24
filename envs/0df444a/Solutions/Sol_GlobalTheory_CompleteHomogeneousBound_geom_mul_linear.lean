-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.geom_mul_linear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:56.512637+00:00
-- url     : https://prove2.me/submissions/0b164549-9923-4d1e-a45b-c5f911278599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
open GlobalTheory GlobalTheory.CompleteHomogeneousBound
namespace GlobalTheory.CompleteHomogeneousBound
theorem _root_.solution (b : ℂ) : (mk fun m => b ^ m : ℂ⟦X⟧) * (1 - C b * X) = 1 := by
  ext m
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases m with
  | zero => simp
  | succ m => simp [coeff_succ_mul_X, coeff_one, pow_succ]
end GlobalTheory.CompleteHomogeneousBound
