-- Prove2me | solution 1 for GlobalTheory.GroupGlue.exists_oAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:05.752249+00:00
-- url     : https://prove2.me/submissions/67b3b5c3-7b51-45fb-a726-a614ee6fc1f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_exists_lift
import Theorems.Thm_GlobalTheory_GroupGlue_exists_endo
import Theorems.Thm_GlobalTheory_GroupGlue_MulCompat_one
import Theorems.Thm_GlobalTheory_GroupGlue_over_ext
import Theorems.Thm_GlobalTheory_GroupGlue_exists_rep
import Theorems.Thm_GlobalTheory_GroupGlue_rep_mul
import Theorems.Thm_GlobalTheory_GroupGlue_isMonHom_of_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
variable [GrpObj G]
namespace GlobalTheory.GroupGlue
theorem _root_.solution {O : Type} [CommRing O] (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) (α : ∀ i, OAct O (H i))
    (he : ∀ (x : O) (i j : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (a : Over.mk u ⟶ H i)
      (b : Over.mk v ⟶ H j), a.left ≫ ψ i = b.left ≫ ψ j →
        (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α j).act x).left ≫ ψ j) :
    ∃ A : OAct O G, ∀ x i, ((α i).act x).left ≫ ψ i = ψ i ≫ (A.act x).left := by
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := fun i => (h i).1
  choose E hE using fun x => exists_endo hψ (fun i => (α i).act x) (he x)
  have hE' : ∀ x i, ((α i).act x).left ≫ ψ i = ψ i ≫ (E x).left := hE
  have hE'' : ∀ x i {Z : Scheme.{0}} (k : G.left ⟶ Z), ((α i).act x).left ≫ ψ i ≫ k = ψ i ≫ (E x).left ≫ k := by
    intro x i Z k
    rw [← Category.assoc, hE', Category.assoc]
  have uniqE : ∀ F F' : G ⟶ G, (∀ i, ψ i ≫ F.left = ψ i ≫ F'.left) → F = F' := by
    intro F F' hF
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_lift hψ i u g hu
    rw [← ha, Category.assoc, Category.assoc, hF i]
  have hmon : ∀ x, IsMonHom (E x) := by
    intro x
    refine isMonHom_of_points (E x) fun T y z => ?_
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu y
    obtain ⟨b, hb⟩ := exists_rep hψ hu z
    have := (α i).hom x
    have hay : (a ≫ (α i).act x).left ≫ ψ i = g ≫ (y ≫ E x).left := by
      rw [Over.comp_left, Category.assoc, hE', ← Category.assoc, ha]
      simp
    have hbz : (b ≫ (α i).act x).left ≫ ψ i = g ≫ (z ≫ E x).left := by
      rw [Over.comp_left, Category.assoc, hE', ← Category.assoc, hb]
      simp
    rw [Over.comp_left, ← Category.assoc, ← rep_mul h hu ha hb, ← rep_mul h hu hay hbz, Category.assoc,
      ← hE', ← Category.assoc, ← Over.comp_left, MonObj.mul_comp]
  refine ⟨{ act := E, hom := hmon, one := ?_, mul := ?_, add := ?_ }, hE'⟩
  · apply uniqE
    intro i
    rw [← hE', (α i).one]
    simp
  · intro x y
    apply uniqE
    intro i
    rw [← hE', (α i).mul]
    simp only [Over.comp_left, Category.assoc, hE', hE'']
  · intro x y
    apply uniqE
    intro i
    let k : Over.mk (H i).hom ⟶ H i := Over.homMk (𝟙 _) (by simp)
    have e2 := rep_mul h (hψ i).w.symm (a := k ≫ (α i).act x) (b := k ≫ (α i).act y) (x := E x) (y := E y)
      (by simp [k, hE']) (by simp [k, hE'])
    rw [← e2, ← MonObj.comp_mul, ← (α i).add, ← hE']
    simp [k]
end GlobalTheory.GroupGlue
