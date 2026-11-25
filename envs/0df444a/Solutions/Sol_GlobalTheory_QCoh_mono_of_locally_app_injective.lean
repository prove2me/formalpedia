-- Prove2me | solution 1 for GlobalTheory.QCoh.mono_of_locally_app_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:04.023943+00:00
-- url     : https://prove2.me/submissions/ea89c627-691d-4dfe-bf2d-4edb34e0382a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_hom_app_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : F ⟶ F')
    (h : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
      Function.Injective (φ.app U)) : Mono φ := by
  refine (Scheme.Modules.toPresheaf X).mono_of_mono_map ((NatTrans.mono_iff_mono_app _).mpr ?_)
  rintro ⟨W⟩
  refine (AddCommGrpCat.mono_iff_injective _).mpr fun s t e ↦ ?_
  choose 𝒰 hx hle hinj using fun x : W ↦ h W x x.2
  refine section_eq_of_cover F 𝒰 hle (fun x hxW ↦ Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hx _⟩) s t
    fun i ↦ hinj i ?_
  refine (hom_app_res φ (hle i) s).trans (Eq.trans ?_ (hom_app_res φ (hle i) t).symm)
  exact congr(F'.presheaf.map (homOfLE (hle i)).op $e)
end GlobalTheory.QCoh
