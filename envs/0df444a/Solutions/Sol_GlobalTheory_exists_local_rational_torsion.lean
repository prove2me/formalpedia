-- Prove2me | solution 1 for GlobalTheory.exists_local_rational_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:52.308794+00:00
-- url     : https://prove2.me/submissions/3d674176-be1a-4181-af89-a9f2643f71ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_section_of_etale
import Theorems.Thm_GlobalTheory_exists_section_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (n : ℕ) [Etale (mulA A n).left]
    {Z : Over (Spec (CommRingCat.of K))} (d : Z ⟶ A) (hd : d ^ n = 1) (p : Z.left) :
    ∃ (W : Over (Spec (CommRingCat.of K))) (c : W ⟶ Z) (_ : IsOpenImmersion c.left),
      p ∈ Set.range c.left ∧ ∃ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A,
        y ^ n = 1 ∧ c ≫ d = toUnit W ≫ y := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of K))},
      (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have e : d.left ≫ (mulA A n).left = Z.hom ≫ η[A].left := by
    rw [← Over.comp_left, hmul, hd, hone]
  let l : Z.left ⟶ pullback (mulA A n).left η[A].left := pullback.lift _ _ e
  obtain ⟨s, hs, t, ht⟩ := exists_section_of_etale (K := K)
    (pullback.snd (mulA A n).left η[A].left) (l p)
  have := isOpenImmersion_of_section_of_etale (pullback.snd (mulA A n).left η[A].left) s hs
  have hy : (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ A.hom = 𝟙 _ := by
    rw [← Over.w (mulA A n), Category.assoc, pullback.condition_assoc]
    erw [hη]
    exact (congrArg (s ≫ ·) (Category.comp_id _)).trans hs
  let y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A := Over.homMk _ hy
  refine ⟨Over.mk (pullback.fst l s ≫ Z.hom), Over.homMk (pullback.fst l s) rfl,
    inferInstanceAs (IsOpenImmersion (pullback.fst l s)), ?_, y, ?_, ?_⟩
  · obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := l) (g := s) p t ht.symm
    exact ⟨w, hw⟩
  · rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    change (s ≫ pullback.fst (mulA A n).left η[A].left) ≫ (mulA A n).left = 𝟙 _ ≫ η[A].left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ η[A].left) hs
  · apply Over.OverMorphism.ext
    change pullback.fst l s ≫ d.left =
      (pullback.fst l s ≫ Z.hom) ≫ s ≫ pullback.fst (mulA A n).left η[A].left
    have h1 : d.left = l ≫ pullback.fst (mulA A n).left η[A].left := (pullback.lift_fst _ _ _).symm
    have h2 : Z.hom = l ≫ pullback.snd (mulA A n).left η[A].left := (pullback.lift_snd _ _ _).symm
    have h3 : pullback.fst l s ≫ Z.hom = pullback.snd l s := by
      rw [h2, pullback.condition_assoc]
      exact (congrArg (pullback.snd l s ≫ ·) hs).trans (Category.comp_id _)
    rw [h3, h1, pullback.condition_assoc]
end GlobalTheory
