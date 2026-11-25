-- Prove2me | solution 1 for GlobalTheory.QCoh.topologicalKrullDim_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:50.048919+00:00
-- url     : https://prove2.me/submissions/4b37a0e0-01d4-4880-ac74-1446b245b2ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_mono
import Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_le_of_isIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {T : Type*} [TopologicalSpace T] {s t : Set T}
    (hs : IsClosed s) (ht : IsClosed t) :
    topologicalKrullDim (s ∪ t :) = max (topologicalKrullDim s) (topologicalKrullDim t) := by
  refine le_antisymm (topologicalKrullDim_le_of_isIrreducible fun Z hZ hirr ↦ ?_)
    (max_le (topologicalKrullDim_mono Set.subset_union_left)
      (topologicalKrullDim_mono Set.subset_union_right))
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 hirr.2 s t hs ht hZ with h | h
  · exact (topologicalKrullDim_mono h).trans (le_max_left _ _)
  · exact (topologicalKrullDim_mono h).trans (le_max_right _ _)
end GlobalTheory.QCoh
