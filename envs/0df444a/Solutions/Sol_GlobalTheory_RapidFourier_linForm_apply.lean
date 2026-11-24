-- Prove2me | solution 1 for GlobalTheory.RapidFourier.linForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:41.544961+00:00
-- url     : https://prove2.me/submissions/22589f27-a908-4cef-aeb4-e3098cc32abc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    linForm ν x = ∑ k, (ν k : ℝ) * x k := by
  simp [linForm]
end GlobalTheory.RapidFourier
