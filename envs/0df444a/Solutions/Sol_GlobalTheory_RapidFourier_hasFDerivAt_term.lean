-- Prove2me | solution 1 for GlobalTheory.RapidFourier.hasFDerivAt_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:37.929825+00:00
-- url     : https://prove2.me/submissions/eee04ab6-4e2e-4441-835e-0a3629463d09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Theorems.Thm_GlobalTheory_RapidFourier_hasDerivAt_wave

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
theorem _root_.solution {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (wave a ∘ linForm ν)
      ((linForm ν).smulRight (wave (2 * π * I * a) (linForm ν x))) x := by
  have h := (hasDerivAt_wave a (linForm ν x)).hasFDerivAt.comp x (linForm ν).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp
end GlobalTheory.RapidFourier
