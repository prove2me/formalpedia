-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_locallyConstantCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:17.24685+00:00
-- url     : https://prove2.me/submissions/0e57dc8f-47f6-4411-82f4-b4bd8453dc47

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
open scoped Pointwise
variable (X : Type*) [TopologicalSpace X] (R E : Type*) [Semiring R] [AddCommMonoid E]
  [Module R E]
variable {X R E}
namespace GroundTheory.Automorphic
theorem _root_.solution {f : X → E} :
    f ∈ locallyConstantCompactSupport X R E ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl
end GroundTheory.Automorphic
