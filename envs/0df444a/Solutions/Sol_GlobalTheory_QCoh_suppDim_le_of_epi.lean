-- Prove2me | solution 1 for GlobalTheory.QCoh.suppDim_le_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:04.188822+00:00
-- url     : https://prove2.me/submissions/2191d746-4c0f-4fc5-85a9-cbe1c3360d3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_support_subset_of_epi
import Theorems.Thm_GlobalTheory_QCoh_suppDim_le_of_support_subset

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
theorem _root_.solution (φ : F ⟶ G) [Epi φ] : suppDim G ≤ suppDim F :=
  suppDim_le_of_support_subset (support_subset_of_epi φ)
end GlobalTheory.QCoh
