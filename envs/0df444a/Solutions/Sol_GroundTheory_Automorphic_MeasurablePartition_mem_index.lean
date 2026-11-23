-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.mem_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:08.13839+00:00
-- url     : https://prove2.me/submissions/77cc77ae-3d26-47e7-add3-581150ad53db

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition

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
theorem _root_.solution (x : X) : x ∈ p.E (p.index x) := by
  classical exact (Nat.find_spec (p.exists_mem x)).2
end GroundTheory.Automorphic.MeasurablePartition
