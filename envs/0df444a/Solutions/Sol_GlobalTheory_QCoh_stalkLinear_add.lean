-- Prove2me | solution 1 for GlobalTheory.QCoh.stalkLinear_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:58:35.69588+00:00
-- url     : https://prove2.me/submissions/a564c56f-93aa-4ce1-9c8c-ee3b96fb0352

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime

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
theorem _root_.solution (φ ψ : F ⟶ G) (x : X) :
    stalkLinear (φ + ψ) x = stalkLinear φ x + stalkLinear ψ x := by
  ext t
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [LinearMap.add_apply, stalkLinear_germ, stalkLinear_germ, stalkLinear_germ, ← map_add]; rfl
end GlobalTheory.QCoh
