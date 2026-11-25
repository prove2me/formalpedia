-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_iff_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:06:24.540544+00:00
-- url     : https://prove2.me/submissions/5690f163-31a1-45b5-a18f-af5f1830c5e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_forall_affine
import Theorems.Thm_GlobalTheory_QCoh_isBaseChange_resLinear

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
    F.IsQuasicoherent ↔ ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → ∀ h : V ≤ U,
      letI := resAlgebra h
      letI := resModule F h
      haveI := res_isScalarTower F h
      IsBaseChange Γ(X, V) (resLinear F h) := by
  refine ⟨fun _ _ _ hU hV h ↦ isBaseChange_resLinear F hU hV h, fun H ↦ ?_⟩
  refine (isQuasicoherent_iff_forall_affine F).mpr fun U hU f ↦ ?_
  haveI := hU.isLocalization_basicOpen f
  exact (isLocalizedModule_iff_isBaseChange (.powers f) Γ(X, X.basicOpen f) _).mpr
    (H U _ hU (hU.basicOpen f) (X.basicOpen_le f))
end GlobalTheory.QCoh
