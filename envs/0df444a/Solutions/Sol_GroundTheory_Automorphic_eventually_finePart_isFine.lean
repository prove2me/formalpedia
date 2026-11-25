-- Prove2me | solution 1 for GroundTheory.Automorphic.eventually_finePart_isFine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:50.486872+00:00
-- url     : https://prove2.me/submissions/e7808bce-dcd5-4217-a1b0-75da92870e04

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_IsFine_mono
import Theorems.Thm_GroundTheory_Automorphic_eventually_fineFilter
import Theorems.Thm_GroundTheory_Automorphic_finePart_isFine

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
theorem _root_.solution {W : SetRel X X} (hW : W ∈ 𝓤 X) :
    ∀ᶠ V in fineFilter X, (finePart V).IsFine W := by
  filter_upwards [eventually_fineFilter hW] with V hV
  exact (finePart_isFine hV.2).mono hV.1
end GroundTheory.Automorphic
