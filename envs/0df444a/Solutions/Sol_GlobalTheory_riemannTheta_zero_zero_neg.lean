-- Prove2me | solution 1 for GlobalTheory.riemannTheta_zero_zero_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:28.293834+00:00
-- url     : https://prove2.me/submissions/25da4403-d76c-49b9-b1ef-58bee5754f7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
namespace GlobalTheory
theorem _root_.solution (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta 0 0 Ω (-v) = riemannTheta 0 0 Ω v := by
  rw [riemannTheta_neg, neg_zero]
end GlobalTheory
