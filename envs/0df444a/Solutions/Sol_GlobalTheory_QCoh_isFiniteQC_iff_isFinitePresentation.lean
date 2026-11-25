-- Prove2me | solution 1 for GlobalTheory.QCoh.isFiniteQC_iff_isFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:48.713432+00:00
-- url     : https://prove2.me/submissions/ca0c21e1-2510-4684-9e7c-617aaccfdc3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_isFinitePresentation
import Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_isFinitePresentation

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
theorem _root_.solution [IsLocallyNoetherian X] :
    IsFiniteQC F ↔ F.IsFinitePresentation :=
  ⟨fun _ ↦ IsFiniteQC.isFinitePresentation, fun _ ↦ .of_isFinitePresentation⟩
end GlobalTheory.QCoh
