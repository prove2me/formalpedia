-- Prove2me | solution 1 for GlobalTheory.IsSiegel.continuous_riemannTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:00:39.04312+00:00
-- url     : https://prove2.me/submissions/13b8acf4-d7c0-42f8-98fd-11ef8432967b

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
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) : Continuous (riemannTheta a b Ω) :=
  (h.differentiable_riemannTheta a b).continuous
end IsSiegel
end GlobalTheory
