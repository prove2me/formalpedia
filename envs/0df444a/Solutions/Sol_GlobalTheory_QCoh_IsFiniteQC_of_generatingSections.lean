-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.of_generatingSections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:43.120204+00:00
-- url     : https://prove2.me/submissions/a103cc5c-f9b8-431c-8a03-5dcfb687100f

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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
namespace IsFiniteQC
theorem _root_.solution [F.IsQuasicoherent] (σ : F.GeneratingSections)
    [σ.IsFiniteType] : IsFiniteQC F :=
  have : Epi (C := X.Modules) (X := freeModule X σ.I) (Y := F) σ.π := σ.epi
  .of_epi (F := freeModule X σ.I) σ.π
end IsFiniteQC
end GlobalTheory.QCoh
