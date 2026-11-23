-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.index_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:01.184768+00:00
-- url     : https://prove2.me/submissions/e83e9eb8-6f90-42ca-9e6e-43a4e23b75ae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_mem_index

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology Uniformity UniformSpace Function
open GroundTheory.Automorphic.MeasurablePartition
variable {X : Type*} [MeasurableSpace X]
variable (p : MeasurablePartition X)
namespace GroundTheory.Automorphic.MeasurablePartition
theorem _root_.solution {x : X} {i : ℕ} : p.index x = i ↔ x ∈ p.E i := by
  refine ⟨fun h => h ▸ p.mem_index x, fun h => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (p.disjoint hne) (p.mem_index x) h
end GroundTheory.Automorphic.MeasurablePartition
