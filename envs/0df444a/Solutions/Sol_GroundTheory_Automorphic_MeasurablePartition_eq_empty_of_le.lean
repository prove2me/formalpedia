-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.eq_empty_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:24.513881+00:00
-- url     : https://prove2.me/submissions/c41b2d01-639c-4077-896d-ed9a924ae8a6

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
theorem _root_.solution {i : ℕ} (hi : p.n ≤ i) : p.E i = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨j, hj, hxj⟩ := p.exists_mem x
  exact Set.disjoint_left.1 (p.disjoint (show j ≠ i by omega)) hxj hx
end GroundTheory.Automorphic.MeasurablePartition
