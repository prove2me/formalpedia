-- Prove2me | solution 1 for GlobalTheory.QCoh.topologicalKrullDim_le_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:05.904455+00:00
-- url     : https://prove2.me/submissions/a8823c22-2b83-4233-bd1a-9bea5004c749

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_topologicalKrullDim_le_of_irreducibleCloseds

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
theorem _root_.solution {T : Type*} [TopologicalSpace T] {s : Set T}
    {d : WithBot ℕ∞} (h : ∀ Z ⊆ s, IsIrreducible Z → topologicalKrullDim Z ≤ d) :
    topologicalKrullDim s ≤ d := by
  refine topologicalKrullDim_le_of_irreducibleCloseds fun Z ↦ le_trans ?_
    (h (Subtype.val '' (Z : Set s)) (Subtype.coe_image_subset _ _)
      (Z.isIrreducible.image _ continuous_subtype_val.continuousOn))
  exact (Topology.IsEmbedding.subtypeVal.homeomorphImage
    (Z : Set s)).isInducing.topologicalKrullDim_le
end GlobalTheory.QCoh
