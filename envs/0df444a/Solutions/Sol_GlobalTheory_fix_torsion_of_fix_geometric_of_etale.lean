-- Prove2me | solution 1 for GlobalTheory.fix_torsion_of_fix_geometric_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:06:10.646124+00:00
-- url     : https://prove2.me/submissions/3211e99e-9dea-4564-afba-50411673f511

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqOfDominantGeometricPointsOfUnramified
import Theorems.Thm_GlobalTheory_eq_of_dominant_geometric_points_of_unramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : ℕ)
    [Etale (mulA A M).left] [IsSeparated (mulA A M).left]
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : A ⟶ A) [IsMonHom s]
    (hs : ∀ x : Over.mk t ⟶ A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ A) (hx : x ^ M = 1) : x ≫ s = x := by
  have hmul : ∀ {Z : Over S} (y : Z ⟶ A), y ≫ mulA A M = y ^ M := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over S}, (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let K : Over S := Over.mk (pullback.snd (mulA A M).left η[A].left)
  have hη : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  let i : K ⟶ A := Over.homMk (pullback.fst (mulA A M).left η[A].left) (by
    change pullback.fst (mulA A M).left η[A].left ≫ A.hom = pullback.snd (mulA A M).left η[A].left
    rw [← Over.w (mulA A M), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hi : i ^ M = 1 := by
    rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    exact pullback.condition
  have hlift : ∀ {Z : Over S} (y : Z ⟶ A), y ^ M = 1 → ∃ l : Z ⟶ K, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA A M).left = Z.hom ≫ η[A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over S} (l l' : Z ⟶ K), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  obtain ⟨σ, hσ⟩ := hlift (i ≫ s) (by rw [← MonObj.pow_comp, hi, MonObj.one_comp])
  have hEt : Etale K.hom := inferInstanceAs (Etale (pullback.snd (mulA A M).left η[A].left))
  have hSep : IsSeparated K.hom :=
    inferInstanceAs (IsSeparated (pullback.snd (mulA A M).left η[A].left))
  have key : σ = 𝟙 K := by
    apply Over.OverMorphism.ext
    refine eq_of_dominant_geometric_points_of_unramified K.hom K.hom (Over.w σ) (Over.w (𝟙 K)) t ?_
    intro j hj
    let j' : Over.mk t ⟶ K := Over.homMk j hj
    have : j' ≫ σ = j' ≫ 𝟙 K := by
      apply hmono
      rw [Category.assoc, hσ, Category.comp_id, ← Category.assoc]
      exact hs _ (by rw [← MonObj.comp_pow, hi, MonObj.comp_one])
    exact congr(($this).left)
  obtain ⟨l, rfl⟩ := hlift x hx
  rw [Category.assoc, ← hσ, key, Category.id_comp]
end GlobalTheory
