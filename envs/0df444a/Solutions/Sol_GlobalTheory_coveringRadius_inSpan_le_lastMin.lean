-- Prove2me | solution 1 for GlobalTheory.coveringRadius_inSpan_le_lastMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:14.817783+00:00
-- url     : https://prove2.me/submissions/7e4ef1db-0613-4a82-aaf4-96041799bbde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
import Theorems.Thm_GlobalTheory_coveringRadius_le_lastMin
import Theorems.Thm_GlobalTheory_finrank_span_eq_finrank_int
import Theorems.Thm_GlobalTheory_lastMin_inSpan


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] : coveringRadius (inSpan L) ≤ √(finrank ℤ L) / 2 * lastMin L := by
  have := coveringRadius_le_lastMin (inSpan L)
  rwa [lastMin_inSpan, finrank_span_eq_finrank_int] at this
end GlobalTheory
