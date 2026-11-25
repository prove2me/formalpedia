-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.IsFine.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:26.125912+00:00
-- url     : https://prove2.me/submissions/09b3a6fc-83c0-4a47-8a2e-0e4e94d756cc

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
variable {p}
namespace GroundTheory.Automorphic.MeasurablePartition
namespace IsFine
theorem _root_.solution {V W : SetRel X X} (h : p.IsFine V) (hVW : V ⊆ W) : p.IsFine W :=
  fun i x hx y hy => hVW (h i x hx y hy)
end IsFine
end GroundTheory.Automorphic.MeasurablePartition
