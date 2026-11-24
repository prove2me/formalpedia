-- Prove2me | solution 1 for GlobalTheory.IsSiegel.hasSum_riemannTheta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:50.1605+00:00
-- url     : https://prove2.me/submissions/d5e1c245-8cf6-4018-bcbd-b22e8d3a3d64

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
    (a b : ι → ℝ) (v : ι → ℂ) : HasSum (riemannThetaTerm a b Ω v) (riemannTheta a b Ω v) :=
  (h.summable_riemannThetaTerm a b v).hasSum
end IsSiegel
end GlobalTheory
