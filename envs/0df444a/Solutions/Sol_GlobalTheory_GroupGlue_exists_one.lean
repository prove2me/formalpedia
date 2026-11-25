-- Prove2me | solution 1 for GlobalTheory.GroupGlue.exists_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:04:50.298984+00:00
-- url     : https://prove2.me/submissions/679451f6-7891-4e84-84e9-23e86198a6fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_ext_small
import Theorems.Thm_GlobalTheory_GroupGlue_exists_glue
import Theorems.Thm_GlobalTheory_GroupGlue_base_eq
import Theorems.Thm_GlobalTheory_GroupGlue_MulCompat_one
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
variable [∀ i, GrpObj (H i)]
namespace GlobalTheory.GroupGlue
theorem _root_.solution (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) :
    ∃ e : 𝟙_ (Over X) ⟶ G, ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (T : Over X)
      (g : S ⟶ T.left), u ≫ 𝒰.f i = g ≫ T.hom →
        (1 : Over.mk u ⟶ H i).left ≫ ψ i = g ≫ (toUnit T ≫ e).left := by
  obtain ⟨z, hz⟩ := exists_glue 𝒰 (𝟙_ (Over X)).hom
    (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ (𝟙_ (Over X)).hom ∧
      (1 : Over.mk u ⟶ H i).left ≫ ψ i = w)
    (fun i S g u hu => ⟨_, i, u, hu, rfl⟩)
    (fun S S' k g _ ⟨i, u, hu, hw⟩ => ⟨i, k ≫ u, by simp [hu], by
      have e0 : (1 : Over.mk (k ≫ u) ⟶ H i) = res k u ≫ 1 := (MonObj.comp_one _).symm
      rw [e0, ← hw, Over.comp_left, Category.assoc]
      rfl⟩)
    (fun S g w w' ⟨i, u, hu, hw⟩ ⟨j, v, hv, hw'⟩ => by
      rw [← hw, ← hw']
      exact MulCompat.one hm hψ u v (hu.trans hv.symm))
  have hzG : z ≫ G.hom = (𝟙_ (Over X)).hom := by
    refine ext_small 𝒰 (𝟙_ (Over X)).hom fun i S g u hu => ?_
    rw [← Category.assoc, hz S g _ ⟨i, u, hu, rfl⟩, ← base_eq hψ (1 : Over.mk u ⟶ H i)]
    exact hu
  refine ⟨Over.homMk z hzG, fun i S u T g hg => ?_⟩
  have e1 := hz S (g ≫ (toUnit T).left) _ ⟨i, u, by rw [hg, Category.assoc, Over.w], rfl⟩
  rw [← e1]
  simp
end GlobalTheory.GroupGlue
