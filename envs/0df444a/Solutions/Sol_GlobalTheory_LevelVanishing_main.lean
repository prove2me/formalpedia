-- Prove2me | solution 1 for GlobalTheory.LevelVanishing.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:39.27266+00:00
-- url     : https://prove2.me/submissions/e6edd08f-c909-4603-a856-3b2b5bc4c842

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FromSpecStalkComp
import Theorems.Thm_GlobalTheory_LevelVanishing_sval_mem_map
import Theorems.Thm_GlobalTheory_LiftTest_main
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory GlobalTheory.LevelVanishing
namespace GlobalTheory.LevelVanishing
theorem _root_.solution : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) f, U.ExpT (𝟙_ _) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ α ∉ s, ∀ (z : (𝟙_ _ ⊗ D.P.A).left) (J), Good D.P.L z J → sval (f α) (𝟙 _) z J ∈ (IsLocalRing.maximalIdeal V ^ (e + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))) := by
  intro V _ _ _ _ D A G _ _ U k σ f h e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun α hα z J hJ => sval_mem_map _ (𝟙_ _ ⊗ D.P.A).hom D.P.isLB (f α) ?_ z J hJ⟩
  refine GlobalTheory.LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f α) ?_
  intro Z x r hr z J hJ
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  have hb : r ≫ (𝟙_ _ ⊗ D.P.A).hom = x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left ≫ G.hom := by
    rw [← Over.w (snd (𝟙_ _) D.P.A), ← Category.assoc, hr, Category.assoc, Over.w, Over.w]
  let xG : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ G :=
    Over.homMk (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) (by rw [Category.assoc]; exact hb.symm)
  let rB : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r
  refine (hs Z x (lift (rB ≫ fst _ _) xG).left r ?_ hr ?_ z JG J hJG hJ).1 α hα
  · exact congrArg CommaMorphism.left (lift_snd (rB ≫ fst _ _) xG)
  · exact (congrArg CommaMorphism.left (lift_fst (rB ≫ fst _ _) xG)).symm
end GlobalTheory.LevelVanishing
