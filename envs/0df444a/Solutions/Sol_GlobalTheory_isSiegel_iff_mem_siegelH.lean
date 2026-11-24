-- Prove2me | solution 1 for GlobalTheory.isSiegel_iff_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:41.099481+00:00
-- url     : https://prove2.me/submissions/3d432c66-0044-4d8e-bc36-a5a5de4150b6

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
theorem _root_.solution [Fintype ι] {Ω : Matrix ι ι ℂ} :
    IsSiegel Ω ↔ Ω ∈ ReciprocityTheory.PTheta.SiegelH ι := Iff.rfl
end GlobalTheory
