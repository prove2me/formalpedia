-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.of_isFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:46.35243+00:00
-- url     : https://prove2.me/submissions/07e587fb-0f1e-4cde-bd15-027d874d9a41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_isFiniteType

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
theorem _root_.solution [F.IsFinitePresentation] : IsFiniteQC F :=
  .of_isFiniteType
end IsFiniteQC
end GlobalTheory.QCoh
