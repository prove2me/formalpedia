-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:30.189681+00:00
-- url     : https://prove2.me/submissions/24403d8b-b68d-4411-a623-8e82a1b3fcc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_exact_app_of_exact


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
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteQC S.X₁] [S.X₂.IsQuasicoherent] [IsFiniteQC S.X₃] : IsFiniteQC S.X₂ :=
  ⟨inferInstance, fun U hU ↦
    have := hS.epi_g
    have := finite_sections S.X₁ hU
    have := finite_sections S.X₃ hU
    Module.Finite.of_exact (f := appLinear S.f U) (g := appLinear S.g U)
      (exact_app_of_exact hS.exact hU) (surjective_app_of_epi S.g hU)⟩
end IsFiniteQC
end GlobalTheory.QCoh
