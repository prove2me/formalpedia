-- Prove2me | solution 1 for GroundTheory.Automorphic.eventually_fineFilter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:01.916914+00:00
-- url     : https://prove2.me/submissions/e1f16254-0554-43b7-adfd-8dd39da33718

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
namespace GroundTheory.Automorphic
theorem _root_.solution {W : SetRel X X} (hW : W ∈ 𝓤 X) :
    ∀ᶠ V in fineFilter X, V ⊆ W ∧ V ∈ 𝓤 X := by
  have h1 : ∀ᶠ V in (𝓤 X).smallSets, V ⊆ W := eventually_smallSets_subset.2 hW
  exact (h1.filter_mono inf_le_left).and (eventually_inf_principal.2 (Eventually.of_forall
    fun _ hV => hV))
end GroundTheory.Automorphic
