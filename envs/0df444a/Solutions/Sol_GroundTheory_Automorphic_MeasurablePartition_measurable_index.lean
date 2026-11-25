-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.measurable_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:23.581846+00:00
-- url     : https://prove2.me/submissions/1a6abfa4-028b-446c-af49-105ce5788070

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_index_eq_iff

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
theorem _root_.solution : Measurable p.index := by
  refine measurable_to_countable' fun i => ?_
  have : p.index ⁻¹' {i} = p.E i := by ext x; simp [p.index_eq_iff]
  rw [this]
  exact p.measurableSet i
end GroundTheory.Automorphic.MeasurablePartition
