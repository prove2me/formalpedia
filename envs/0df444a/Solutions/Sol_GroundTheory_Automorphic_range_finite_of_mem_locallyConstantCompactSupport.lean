-- Prove2me | solution 1 for GroundTheory.Automorphic.range_finite_of_mem_locallyConstantCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.218679+00:00
-- url     : https://prove2.me/submissions/e5b81c7c-e34c-443c-8dde-1e9f052dc10d

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
theorem _root_.solution {f : X → E}
    (hf : f ∈ locallyConstantCompactSupport X R E) : (range f).Finite := by
  have : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2
  have h1 : (range fun x : tsupport f => f x).Finite :=
    (hf.1.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact mem_insert _ _
end GroundTheory.Automorphic
