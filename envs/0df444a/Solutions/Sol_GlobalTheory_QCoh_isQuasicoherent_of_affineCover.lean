-- Prove2me | solution 1 for GlobalTheory.QCoh.isQuasicoherent_of_affineCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:46.555015+00:00
-- url     : https://prove2.me/submissions/2cfd9e21-2b37-47be-8dea-03f4c5871ae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_restrict_fromSpec_iff
import Theorems.Thm_GlobalTheory_QCoh_nonempty_presentation_over_of_restrict
import Theorems.Thm_P2M_GlobalTheory_QCoh_nonempty_presentation_restrict___3b59af861bdd

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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i))
    (h : ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f)) :
    F.IsQuasicoherent := by
  have H (i : ι) : Nonempty (F.over (𝒰 i)).Presentation := by
    have := (isQuasicoherent_restrict_fromSpec_iff F (haff i)).mpr (h i)
    obtain ⟨P⟩ := nonempty_presentation_restrict_ι F (haff i)
    exact nonempty_presentation_over_of_restrict F P
  refine SheafOfModules.QuasicoherentData.isQuasicoherent (M := F)
    { I := ι, X := 𝒰, coversTop := ?_, presentation := fun i ↦ (H i).some }
  rw [Opens.coversTop_iff]
  exact hcov
end GlobalTheory.QCoh
