-- Prove2me | solution 1 for GlobalTheory.QCoh.isFiniteQC_iff_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:52.110428+00:00
-- url     : https://prove2.me/submissions/1f5bd1c9-e918-4b1f-a8a3-ded256d53ace

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_iso

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
attribute [instance 100] IsFiniteQC.isQuasicoherent
namespace GlobalTheory.QCoh
theorem _root_.solution (e : F ≅ G) : IsFiniteQC F ↔ IsFiniteQC G :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩
end GlobalTheory.QCoh
