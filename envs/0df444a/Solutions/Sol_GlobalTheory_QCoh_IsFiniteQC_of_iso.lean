-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:17.143265+00:00
-- url     : https://prove2.me/submissions/b99313fe-a4e0-42a2-a87d-dddf836c0727

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
attribute [instance 100] IsFiniteQC.isQuasicoherent
namespace GlobalTheory.QCoh
namespace IsFiniteQC
theorem _root_.solution (e : F ≅ G) [IsFiniteQC F] : IsFiniteQC G :=
  have : G.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e IsFiniteQC.isQuasicoherent
  .of_epi e.hom
end IsFiniteQC
end GlobalTheory.QCoh
