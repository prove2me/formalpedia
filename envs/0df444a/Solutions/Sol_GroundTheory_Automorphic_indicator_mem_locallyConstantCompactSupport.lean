-- Prove2me | solution 1 for GroundTheory.Automorphic.indicator_mem_locallyConstantCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:15.239195+00:00
-- url     : https://prove2.me/submissions/88685bab-c050-4de0-9019-850d35f26ebf

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
theorem _root_.solution [T2Space X] {U : Set X} (hc : IsCompact U)
    (ho : IsOpen U) (e : E) :
    U.indicator (fun _ => e) ∈ locallyConstantCompactSupport X R E := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const X e) ⟨hc.isClosed, ho⟩).isLocallyConstant
end GroundTheory.Automorphic
