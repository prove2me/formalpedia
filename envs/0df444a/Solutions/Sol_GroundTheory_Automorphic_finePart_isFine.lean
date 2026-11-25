-- Prove2me | solution 1 for GroundTheory.Automorphic.finePart_isFine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:53.793375+00:00
-- url     : https://prove2.me/submissions/36b594ad-d0ea-4ae7-bf25-a63cf4f12be0

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
open MeasurablePartition
variable (X : Type*) [UniformSpace X]
variable {X}
variable [MeasurableSpace X] [CompactSpace X] [OpensMeasurableSpace X]
namespace GroundTheory.Automorphic
theorem _root_.solution {V : SetRel X X} (hV : V ∈ 𝓤 X) : (finePart V).IsFine V := by
  classical
  simp only [finePart, dif_pos hV]
  exact (exists_isFine hV).choose_spec
end GroundTheory.Automorphic
