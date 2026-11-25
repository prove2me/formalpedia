-- Prove2me | solution 1 for GlobalTheory.IsSiegel.of_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:02.780726+00:00
-- url     : https://prove2.me/submissions/f2c3beb2-6464-4a1e-b79f-74be1ca001f6

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
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution [Fintype ι] {Ω : Matrix ι ι ℂ}
    (h : Ω ∈ ReciprocityTheory.PTheta.SiegelH ι) : IsSiegel Ω := h
end IsSiegel
end GlobalTheory
