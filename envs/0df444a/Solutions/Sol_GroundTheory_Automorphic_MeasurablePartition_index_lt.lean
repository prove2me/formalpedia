-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.index_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:22.65605+00:00
-- url     : https://prove2.me/submissions/6b8499e2-01f2-4d84-afc3-8ff8df73518b

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
theorem _root_.solution (x : X) : p.index x < p.n := by
  classical exact (Nat.find_spec (p.exists_mem x)).1
end GroundTheory.Automorphic.MeasurablePartition
