-- Prove2me | solution 1 for GlobalTheory.RingGlue.exists_hom_of_ring_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:42:14.864445+00:00
-- url     : https://prove2.me/submissions/2e9c8ff3-253e-47e0-a5ad-07726c1eca6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Theorems.Thm_GlobalTheory_RingGlue_homOfLE_loc
import Theorems.Thm_GlobalTheory_RingGlue_appLE_of_loc
import Theorems.Thm_GlobalTheory_UU_TorusCompat_of_comp
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.RingGlue
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.RingGlue
theorem _root_.solution : (∀ (Y B : Scheme.{0}) (κ : Type) (W : κ → Y.Opens) (V : κ → B.Opens), (∀ k, IsAffineOpen (V k)) → ∀ (ψ : ∀ k, Γ(B, V k) ⟶ Γ(Y, W k)), (∀ y : Y, ∃ k, y ∈ W k) → (∀ (k l : κ) (y : Y), y ∈ W k → y ∈ W l → ∃ (m : κ) (h : W m ≤ W k) (h' : W m ≤ W l) (e : V m ≤ V k) (e' : V m ≤ V l), y ∈ W m ∧ B.presheaf.map (homOfLE e).op ≫ ψ m = ψ k ≫ Y.presheaf.map (homOfLE h).op ∧ B.presheaf.map (homOfLE e').op ≫ ψ m = ψ l ≫ Y.presheaf.map (homOfLE h').op) → ∃ q : Y ⟶ B, ∀ k, ∃ h : W k ≤ q ⁻¹ᵁ V k, q.appLE (V k) (W k) h = ψ k) := by
  intro Y B κ W V hV ψ hc hbas
  let 𝒱 : Y.OpenCover := Y.openCoverOfIsOpenCover W (by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hc y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩)
  let q : Y ⟶ B := 𝒱.glueMorphisms (fun k ↦ loc (hV k) (ψ k)) (by
    intro k l
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f k) (𝒱.f l) x).1 = (pullback.snd (𝒱.f k) (𝒱.f l) x).1 :=
      congr($(pullback.condition (f := 𝒱.f k) (g := 𝒱.f l)) x)
    obtain ⟨m, h1, h2, e1, e2, hxW, H1, H2⟩ := hbas k l _ (pullback.fst (𝒱.f k) (𝒱.f l) x).2
      (hx ▸ (pullback.snd (𝒱.f k) (𝒱.f l) x).2)
    let α : (W m).toScheme ⟶ pullback (𝒱.f k) (𝒱.f l) :=
      pullback.lift (Y.homOfLE h1) (Y.homOfLE h2) ((Y.homOfLE_ι h1).trans (Y.homOfLE_ι h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = Y.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = Y.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f k) (𝒱.f l)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2]
      exact (homOfLE_loc (hV k) (hV m) _ _ h1 e1 H1).trans
        (homOfLE_loc (hV l) (hV m) _ _ h2 e2 H2).symm)
  exact ⟨q, fun k ↦ appLE_of_loc (hV k) (ψ k) q (𝒱.ι_glueMorphisms _ _ k)⟩
end GlobalTheory.RingGlue
