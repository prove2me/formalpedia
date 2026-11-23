-- Prove2me | solution 1 for GlobalTheory.NilpotentEval.pow_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:45.489916+00:00
-- url     : https://prove2.me/submissions/e2d118b3-3e2d-4193-a02d-16a06c242caa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open GlobalTheory.NilpotentEval
variable {A : Type*} [CommRing A]
namespace GlobalTheory.NilpotentEval
theorem _root_.solution {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (n : ℕ) : J ^ (N * n) ≤ K ^ n := by
  rw [pow_mul]
  exact Ideal.pow_right_mono h n
end GlobalTheory.NilpotentEval
