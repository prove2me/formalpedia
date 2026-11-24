-- Prove2me | solution 1 for GroundTheory.Automorphic.isCompact_isOpen_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:12.035712+00:00
-- url     : https://prove2.me/submissions/b8401f87-6b04-41c1-9974-0fe4f6967452

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
theorem _root_.solution {f : X → E} (hf : f ∈ locallyConstantCompactSupport X R E)
    {v : E} (hv : v ≠ 0) : IsCompact {x | f x = v} ∧ IsOpen {x | f x = v} := by
  refine ⟨hf.2.of_isClosed_subset (hf.1.isClosed_fiber v) fun x hx => ?_, hf.1.isOpen_fiber v⟩
  refine subset_tsupport f ?_
  have hx : f x = v := hx
  simp [Function.mem_support, hx, hv]
end GroundTheory.Automorphic
