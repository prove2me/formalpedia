-- Prove2me | solution 1 for GlobalTheory.IsSiegel.mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:46.473368+00:00
-- url     : https://prove2.me/submissions/813ef0b2-237a-4bfa-a695-2b789de9f637

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
theorem _root_.solution {Ω : Matrix ι ι ℂ} (isSymm : Ω.IsSymm) (posDef : (Ω.map Complex.im).PosDef) :
    IsSiegel Ω := ⟨isSymm, posDef⟩
end IsSiegel
end GlobalTheory
