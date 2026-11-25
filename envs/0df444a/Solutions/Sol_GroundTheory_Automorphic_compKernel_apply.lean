-- Prove2me | solution 1 for GroundTheory.Automorphic.compKernel_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:34.504383+00:00
-- url     : https://prove2.me/submissions/330c17bf-bd6b-4686-b613-5c1f410baf85

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTraceComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
namespace GroundTheory.Automorphic
theorem _root_.solution (a b : C(X × X, ℂ)) (z : X × X) :
    compKernel μ a b z = ∫ y, a (z.1, y) * b (y, z.2) ∂μ := rfl
end GroundTheory.Automorphic
