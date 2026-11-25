-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:01:07.783486+00:00
-- url     : https://prove2.me/submissions/a8dd252e-672f-40ba-8bd9-4fe8256033d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
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
theorem _root_.solution
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f)) :
    F.IsQuasicoherent := by
  choose 𝒰 haff hx hloc using h
  refine isQuasicoherent_of_affineCover F 𝒰 ?_ haff hloc
  rw [IsOpenCover, eq_top_iff]
  exact fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩
end GlobalTheory.QCoh
