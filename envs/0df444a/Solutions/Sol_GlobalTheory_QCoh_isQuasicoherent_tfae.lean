-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_tfae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:44.202283+00:00
-- url     : https://prove2.me/submissions/6360378a-32f4-45ee-9370-9bb1461f55f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_affineCover
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_forall_affine

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
    List.TFAE [F.IsQuasicoherent,
      ∀ U : X.Opens, IsAffineOpen U →
        ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f),
      ∃ (ι : Type u) (𝒰 : ι → X.Opens), IsOpenCover 𝒰 ∧ (∀ i, IsAffineOpen (𝒰 i)) ∧
        ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f)] := by
  tfae_have 1 ↔ 2 := isQuasicoherent_iff_forall_affine F
  tfae_have 2 → 3 := fun h ↦
    ⟨X.affineOpens, fun i ↦ i.1, iSup_affineOpens_eq_top X, fun i ↦ i.2, fun i ↦ h i.1 i.2⟩
  tfae_have 3 → 1 := fun ⟨_, 𝒰, hcov, haff, h⟩ ↦ isQuasicoherent_of_affineCover F 𝒰 hcov haff h
  tfae_finish
end GlobalTheory.QCoh
