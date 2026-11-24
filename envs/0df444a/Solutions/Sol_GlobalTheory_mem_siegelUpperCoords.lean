-- Prove2me | solution 1 for GlobalTheory.mem_siegelUpperCoords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:40.859798+00:00
-- url     : https://prove2.me/submissions/5199b9ff-c7fe-47df-8543-fbe31b682579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]
variable {ι : Type*} [LinearOrder ι]
namespace GlobalTheory
theorem _root_.solution {x : {p : ι × ι // p.1 ≤ p.2} → ℂ} :
    x ∈ siegelUpperCoords ι ↔ IsSiegel (symmOfUpper x) := Iff.rfl
end GlobalTheory
