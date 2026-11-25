-- Prove2me | solution 1 for GlobalTheory.QCoh.quasicoherent_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:45.307643+00:00
-- url     : https://prove2.me/submissions/d9b72b67-3b27-4499-ba24-d22d243ad5be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_forall_affine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_affineCover
import Theorems.Thm_GlobalTheory_QCoh_isBaseChange_resLinear
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear

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
theorem _root_.solution :
    (F.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f)) ∧
    (∀ (ι : Type u) (𝒰 : ι → X.Opens), IsOpenCover 𝒰 → (∀ i, IsAffineOpen (𝒰 i)) →
      (F.IsQuasicoherent ↔
        ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f))) ∧
    (F.IsQuasicoherent → ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → ∀ h : V ≤ U,
      letI := resAlgebra h
      letI := resModule F h
      haveI := res_isScalarTower F h
      IsBaseChange Γ(X, V) (resLinear F h)) ∧
    (F.IsQuasicoherent → ∀ (U : X.Opens) (hU : IsAffineOpen U) (x : U),
      IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x)) :=
  ⟨isQuasicoherent_iff_forall_affine F, fun _ ↦ isQuasicoherent_iff_affineCover F,
    fun _ _ _ hU hV h ↦ isBaseChange_resLinear F hU hV h,
    fun _ _ hU x ↦ isLocalizedModule_germLinear F hU x⟩
end GlobalTheory.QCoh
