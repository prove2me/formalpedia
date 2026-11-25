-- Prove2me | solution 1 for GlobalTheory.QCoh.topologicalKrullDim_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:50.919247+00:00
-- url     : https://prove2.me/submissions/a7aab405-4013-4914-90be-757da3fd79f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

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
theorem _root_.solution {T : Type*} [TopologicalSpace T] {s t : Set T} (h : s ⊆ t) :
    topologicalKrullDim s ≤ topologicalKrullDim t :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le
end GlobalTheory.QCoh
