-- Prove2me | solution 1 for GlobalTheory.CoverGlue.isMonHom_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:24:29.452213+00:00
-- url     : https://prove2.me/submissions/acfc350d-2cf7-4737-96a8-d3ec8448bd22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionAndIsMonHomOfOpenCover
import Theorems.Thm_GlobalTheory_CoverGlue_exists_lift
import Theorems.Thm_GlobalTheory_CoverGlue_over_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.CoverGlue
variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens} {A : Over S} [GrpObj A] {G : ∀ i, Over (U i).toScheme}
  [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}
private theorem mul_comp_of_cover_isGrpPullback_isMonHom (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i))
    {T : Over S} (a b : T ⟶ A) : (a * b) ≫ f = (a ≫ f) * (b ≫ f) := by
  refine over_ext hU fun i T' r => ?_
  haveI := hm i
  obtain ⟨a', ha⟩ := exists_lift (hψ i).1 (r ≫ a)
  obtain ⟨b', hb⟩ := exists_lift (hψ i).1 (r ≫ b)
  have e1 := (hψ i).2 T' a' b' (r ≫ a) (r ≫ b) ha hb
  have ha' : (r ≫ a ≫ f).left = (a' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) ha
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have hb' : (r ≫ b ≫ f).left = (b' ≫ f' i).left ≫ ψ i := by
    have := congrArg (· ≫ f.left) hb
    simp only [Over.comp_left, Category.assoc] at this ⊢
    rw [this, hf]
  have e2 := (hψ i).2 T' (a' ≫ f' i) (b' ≫ f' i) (r ≫ a ≫ f) (r ≫ b ≫ f) ha' hb'
  have e3 : (a' * b') ≫ f' i = (a' ≫ f' i) * (b' ≫ f' i) := MonObj.mul_comp _ _ _
  apply Over.OverMorphism.ext
  rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, Over.comp_left, e1, e2, ← e3, Over.comp_left]
  simp only [Category.assoc, hf]
end GlobalTheory.CoverGlue
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens} {A : Over S} [GrpObj A] {G : ∀ i, Over (U i).toScheme}
  [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}
namespace GlobalTheory.CoverGlue
theorem _root_.solution (hU : iSup U = ⊤) (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (f : A ⟶ A)
    (f' : ∀ i, G i ⟶ G i) (hf : ∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) (hm : ∀ i, IsMonHom (f' i)) :
    IsMonHom f := by
  have hmul : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) :=
    fun a b => mul_comp_of_cover_isGrpPullback_isMonHom hU hψ f f' hf hm a b
  have hone : ∀ {T : Over S}, (1 : T ⟶ A) ≫ f = 1 := by
    intro T
    have h1 := hmul (1 : T ⟶ A) 1
    rw [_root_.mul_one] at h1
    exact _root_.mul_eq_left.mp h1.symm
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one]
    exact hone
  · rw [MonObj.mul_eq_mul, hmul, MonObj.comp_mul]
    simp
end GlobalTheory.CoverGlue
