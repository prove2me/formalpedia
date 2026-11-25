-- Prove2me | solution 1 for GlobalTheory.QCoh.restrictPullbackIso_hom_app_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:26.701561+00:00
-- url     : https://prove2.me/submissions/fae9a481-8c96-4d90-a630-3c6f4f9f4873

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections

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
theorem _root_.solution (G : Y.Modules) (V : Y.Opens) (s : Γ(G, V)) :
    ((restrictPullbackIso w).hom.app G).app (j ⁻¹ᵁ f ⁻¹ᵁ V)
      (((Scheme.Modules.pullback p).obj (G.restrict i)).presheaf.map
        (eqToHom (show j ⁻¹ᵁ f ⁻¹ᵁ V = p ⁻¹ᵁ i ⁻¹ᵁ V by
          rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage])).op
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (G.restrict i)).app (i ⁻¹ᵁ V)
          (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s))) =
    ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE (j.image_preimage_le (f ⁻¹ᵁ V))).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s) := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    (((Scheme.Modules.restrictAdjunction i).comp
    (Scheme.Modules.pullbackPushforwardAdjunction p)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp p i ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
        (Scheme.Modules.pushforwardComp j f).symm))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j)) G
  exact congr(($this).app V s)
end GlobalTheory.QCoh
