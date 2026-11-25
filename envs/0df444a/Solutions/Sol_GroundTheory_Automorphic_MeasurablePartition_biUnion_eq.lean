-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.biUnion_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:09.523693+00:00
-- url     : https://prove2.me/submissions/c2eadb36-bc17-4c0f-b6fd-da344030c2f4

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
theorem _root_.solution : ⋃ i ∈ Finset.range p.n, p.E i = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨i, hi, hx⟩ := p.exists_mem x
  exact mem_biUnion (Finset.mem_range.2 hi) hx
end GroundTheory.Automorphic.MeasurablePartition
