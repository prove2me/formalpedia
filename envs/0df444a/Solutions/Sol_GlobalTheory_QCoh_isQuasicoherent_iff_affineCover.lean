-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_iff_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:38.326742+00:00
-- url     : https://prove2.me/submissions/3674bc5c-7c93-40ea-8b84-7a5ae1f2a171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_affineCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i)) :
    F.IsQuasicoherent ↔ ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f) :=
  ⟨fun _ i f ↦ isLocalizedModule_resBasicOpen F (haff i) f,
    isQuasicoherent_of_affineCover F 𝒰 hcov haff⟩
end GlobalTheory.QCoh
