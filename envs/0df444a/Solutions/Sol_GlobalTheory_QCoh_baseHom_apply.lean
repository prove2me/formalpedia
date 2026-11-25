-- Prove2me | solution 1 for GlobalTheory.QCoh.baseHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:06:13.057471+00:00
-- url     : https://prove2.me/submissions/ad42773c-4462-4867-a4a3-09f34e6403ad

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
namespace GlobalTheory.QCoh
theorem _root_.solution (r : R) :
    baseHom U ρ r = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (ρ r) := rfl
end GlobalTheory.QCoh
