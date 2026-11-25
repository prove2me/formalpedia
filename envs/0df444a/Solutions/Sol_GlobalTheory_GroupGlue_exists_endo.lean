-- Prove2me | solution 1 for GlobalTheory.GroupGlue.exists_endo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:05:25.91578+00:00
-- url     : https://prove2.me/submissions/46ea884b-d437-45ce-9aa9-bc70aaba8e02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_ext_small
import Theorems.Thm_GlobalTheory_GroupGlue_exists_glue
import Theorems.Thm_GlobalTheory_GroupGlue_exists_lift
import Theorems.Thm_GlobalTheory_GroupGlue_base_eq
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
namespace GlobalTheory.GroupGlue
theorem _root_.solution (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) (e : ∀ i, H i ⟶ H i)
    (he : ∀ (i j : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (a : Over.mk u ⟶ H i)
      (b : Over.mk v ⟶ H j), a.left ≫ ψ i = b.left ≫ ψ j → (a ≫ e i).left ≫ ψ i = (b ≫ e j).left ≫ ψ j) :
    ∃ E : G ⟶ G, ∀ i, (e i).left ≫ ψ i = ψ i ≫ E.left := by
  obtain ⟨z, hz⟩ := exists_glue 𝒰 G.hom
    (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i), a.left ≫ ψ i = g ∧ (a ≫ e i).left ≫ ψ i = w)
    (fun i S g u hu => by
      obtain ⟨a, ha⟩ := exists_lift hψ i u g hu
      exact ⟨_, i, u, a, ha, rfl⟩)
    (fun S S' k g _ ⟨i, u, a, ha, hw⟩ => ⟨i, k ≫ u, res k u ≫ a, by simp [res, ha], by simp [res, ← hw]⟩)
    (fun S g w w' ⟨i, u, a, ha, hw⟩ ⟨j, v, b, hb, hw'⟩ => by
      rw [← hw, ← hw']
      exact he i j S u v a b (ha.trans hb.symm))
  have hzG : z ≫ G.hom = G.hom := by
    refine ext_small 𝒰 G.hom fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_lift hψ i u g hu
    rw [← Category.assoc, hz S g _ ⟨i, u, a, ha, rfl⟩, ← base_eq hψ (a ≫ e i)]
    exact hu
  refine ⟨Over.homMk z hzG, fun i => ?_⟩
  have e1 := hz _ (ψ i) _ ⟨i, (H i).hom, Over.homMk (𝟙 _) (by simp), by simp, rfl⟩
  simpa using e1.symm
end GlobalTheory.GroupGlue
