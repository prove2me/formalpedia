-- Prove2me | solution 1 for GlobalTheory.QCoh.section_eq_zero_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:58:22.349032+00:00
-- url     : https://prove2.me/submissions/b0646d64-4740-4349-a92c-19e4f16604f2

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
theorem _root_.solution (s : Γ(F, U))
    (h : ∀ (x : X) (hx : x ∈ U), F.presheaf.germ U x hx s = 0) : s = 0 :=
  TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U s 0 fun x hx ↦ by
    rw [map_zero]; exact h x hx
end GlobalTheory.QCoh
