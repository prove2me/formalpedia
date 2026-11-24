-- Prove2me | solution 1 for GlobalTheory.GaussHerm.finrank_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:55.562198+00:00
-- url     : https://prove2.me/submissions/809adc20-b160-44d8-8e56-8cfc2f880f72

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.GaussHerm
namespace GlobalTheory.GaussHerm
theorem _root_.solution (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]
end GlobalTheory.GaussHerm
