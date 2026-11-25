-- Prove2me | solution 1 for GlobalTheory.QCoh.restrictStalkAddEquiv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:45.801817+00:00
-- url     : https://prove2.me/submissions/4caf1d88-9662-4bfb-9c6a-19584177fbf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_restrictStalkAddEquiv_germ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)
    (r : X.presheaf.stalk (g y)) (t : ((F.restrict g).presheaf.stalk y :)) :
    restrictStalkAddEquiv F g y (g.stalkMap y r • t) = r • restrictStalkAddEquiv F g y t := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨W, hW, s, rfl⟩ := (F.restrict g).presheaf.exists_germ_eq t
  have hy : y ∈ W ⊓ g ⁻¹ᵁ U := ⟨hW, hU⟩
  have hle : g ''ᵁ (W ⊓ g ⁻¹ᵁ U) ≤ U := (g.image_mono inf_le_right).trans (g.image_preimage_le U)
  have key : Y.presheaf.map (homOfLE (inf_le_right : W ⊓ g ⁻¹ᵁ U ≤ _)).op (g.app U a) =
      (g.appIso _).hom (X.presheaf.map (homOfLE hle).op a) := by
    have : X.presheaf.map (homOfLE hle).op ≫ (g.appIso _).hom =
        g.app U ≫ Y.presheaf.map (homOfLE (inf_le_right : W ⊓ g ⁻¹ᵁ U ≤ _)).op := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
      rfl
    exact congr($this a).symm
  rw [Scheme.Hom.germ_stalkMap_apply,
    ← Y.presheaf.germ_res_apply (homOfLE (inf_le_right : W ⊓ g ⁻¹ᵁ U ≤ _)) y hy,
    ← (F.restrict g).presheaf.germ_res_apply (homOfLE (inf_le_left : W ⊓ g ⁻¹ᵁ U ≤ _)) y hy,
    ← germ_smul, restrictStalkAddEquiv_germ, restrictStalkAddEquiv_germ,
    ← X.presheaf.germ_res_apply (homOfLE hle) (g y) ⟨y, hy, rfl⟩, key]
  refine Eq.trans ?_ (germ_smul F (U := g ''ᵁ (W ⊓ g ⁻¹ᵁ U)) (g y) ⟨y, hy, rfl⟩ _ _)
  congr 1
  refine (F.smul_restrictAppIso_hom_apply g _ _ _).trans ?_
  rw [Iso.hom_inv_id_apply]
end GlobalTheory.QCoh
