-- Prove2me | solution 1 for GlobalTheory.QCoh.epi_of_locally_app_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:47.776962+00:00
-- url     : https://prove2.me/submissions/97cd7e3f-af0b-42fc-ad77-e1d2510b6a16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_hom_app_res
import Theorems.Thm_GlobalTheory_QCoh_homAppLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


attribute [local simp] GlobalTheory.QCoh.homAppLinear_apply

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : F ⟶ F')
    (h : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
      Function.Surjective (φ.app U)) : Epi φ := by
  refine ⟨fun {H} a b e ↦ Scheme.Modules.hom_ext _ _ fun W ↦ ?_⟩
  ext s
  choose 𝒰 hx hle hsurj using fun x : W ↦ h W x x.2
  refine section_eq_of_cover H 𝒰 hle (fun x hxW ↦ Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hx _⟩) _ _
    fun i ↦ ?_
  obtain ⟨t, ht⟩ := hsurj i (F'.presheaf.map (homOfLE (hle i)).op s)
  refine (hom_app_res a (hle i) s).symm.trans (Eq.trans ?_ (hom_app_res b (hle i) s))
  rw [← ht]
  exact congr(($e).app (𝒰 i) t)
end GlobalTheory.QCoh
