-- Prove2me | solution 1 for GlobalTheory.QCoh.restrictPullbackIso_hom_app_pullbackSections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:18:27.224749+00:00
-- url     : https://prove2.me/submissions/67d9de09-6f24-49ad-b428-777355f6db57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
import Theorems.Thm_GlobalTheory_QCoh_hom_app_res
import Theorems.Thm_GlobalTheory_QCoh_res_pullbackSections
import Theorems.Thm_GlobalTheory_QCoh_pullbackSections_res
import Theorems.Thm_GlobalTheory_QCoh_restrictPullbackIso_hom_app_unit
import Theorems.Thm_GlobalTheory_QCoh_res_res


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
variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {p : X' ⟶ Y'} {j : X' ⟶ X} {i : Y' ⟶ Y}
  [IsOpenImmersion i] [IsOpenImmersion j] (w : p ≫ i = j ≫ f)
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
theorem _root_.solution (G : Y.Modules) {V : Y.Opens} {V' : Y'.Opens}
    {U' : X'.Opens} (hV : i ''ᵁ V' ≤ V) (e' : U' ≤ p ⁻¹ᵁ V') (e : j ''ᵁ U' ≤ f ⁻¹ᵁ V)
    (s : Γ(G, V)) :
    ((restrictPullbackIso w).hom.app G).app U'
      (pullbackSections p (G.restrict i) e' (G.presheaf.map (homOfLE hV).op s)) =
    pullbackSections f G e s := by
  have h₁ : U' ≤ j ⁻¹ᵁ f ⁻¹ᵁ V := (j.preimage_image_eq U').ge.trans (j.preimage_mono e)
  have h₂ : V' ≤ i ⁻¹ᵁ V := (i.preimage_image_eq V').ge.trans (i.preimage_mono hV)
  have h₃ : j ⁻¹ᵁ f ⁻¹ᵁ V ≤ p ⁻¹ᵁ i ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  have H : ((restrictPullbackIso w).hom.app G).app (j ⁻¹ᵁ f ⁻¹ᵁ V)
      (pullbackSections p (G.restrict i) h₃
        (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s)) =
      pullbackSections f G (j.image_preimage_le (f ⁻¹ᵁ V)) s :=
    restrictPullbackIso_hom_app_unit w G V s
  have H₁ := hom_app_res ((restrictPullbackIso w).hom.app G) h₁ (pullbackSections p (G.restrict i)
    h₃ (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s))
  have H₂ := res_pullbackSections p (G.restrict i) h₃ h₁
    (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s)
  have H₃ := pullbackSections_res p (G.restrict i) e' h₂
    (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s)
  have H₄ := res_res G (i.image_preimage_le V) (i.image_mono h₂) s
  have H₅ := res_pullbackSections f G (j.image_preimage_le (f ⁻¹ᵁ V)) (j.image_mono h₁) s
  rw [H] at H₁
  refine Eq.trans ?_ (H₁.trans H₅)
  exact congr(((restrictPullbackIso w).hom.app G).app U'
    $(congr(pullbackSections p (G.restrict i) e' $H₄).symm.trans (H₃.trans H₂.symm)))
end GlobalTheory.QCoh
