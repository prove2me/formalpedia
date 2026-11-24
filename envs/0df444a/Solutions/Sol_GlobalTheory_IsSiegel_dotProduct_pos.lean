-- Prove2me | solution 1 for GlobalTheory.IsSiegel.dotProduct_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:50.717635+00:00
-- url     : https://prove2.me/submissions/468f6065-2233-49d9-9307-b2e7ed8bfb27

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
theorem _root_.solution [Fintype ι] {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {x : ι → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x) := by
  simpa using h.posDef.dotProduct_mulVec_pos hx
end IsSiegel
end GlobalTheory
