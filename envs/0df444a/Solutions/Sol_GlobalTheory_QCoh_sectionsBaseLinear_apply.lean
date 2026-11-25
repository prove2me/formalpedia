-- Prove2me | solution 1 for GlobalTheory.QCoh.sectionsBaseLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:32.052003+00:00
-- url     : https://prove2.me/submissions/e0907a20-3c14-4bc1-92df-89f8ecd11194

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
variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
variable {ρ}
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : F ⟶ G) (s : Γ(F, U)) :
    sectionsBaseLinear ρ φ U s = φ.app U s := rfl
end GlobalTheory.QCoh
