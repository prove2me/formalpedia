-- Prove2me | solution 1 for GlobalTheory.GrpDescent.grpObj_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:49.624818+00:00
-- url     : https://prove2.me/submissions/302a1912-c1e5-4ade-bb07-f1b07711fa44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_GrpObjDescendsFaithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.GrpDescent
variable {S S₀ : Scheme.{0}}
namespace GlobalTheory.GrpDescent
theorem _root_.solution (f : S ⟶ S₀) [Flat f] [Surjective f] (A : Over S) [GrpObj A] (A₀ : Over S₀)
    (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over S₀) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀)
    (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left) (hπ : IsPullback π A.hom A₀.hom f)
    (h1 : π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π) (h2 : π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π)
    (he : η[A].left ≫ π = f ≫ e₀.left) (hm : μ[A].left ≫ π = π₂ ≫ m₀.left)
    (hi : (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left) :
    ∃ _ : GrpObj A₀, IsGrpPullback A A₀ f π := by

  have rmul : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left) {x' y' : T' ⟶ A} {x y : T ⟶ A₀},
      x'.left ≫ π = p ≫ x.left → y'.left ≫ π = p ≫ y.left →
      (x' * y').left ≫ π = p ≫ (lift x y ≫ m₀).left := by
    intro T' T p x' y' x y hx hy
    have : (lift x' y').left ≫ π₂ = p ≫ (lift x y).left := by
      apply pullback.hom_ext
      · change ((lift x' y').left ≫ π₂) ≫ (fst A₀ A₀).left = (p ≫ (lift x y).left) ≫ (fst A₀ A₀).left
        rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
          lift_fst, hx]
      · change ((lift x' y').left ≫ π₂) ≫ (snd A₀ A₀).left = (p ≫ (lift x y).left) ≫ (snd A₀ A₀).left
        rw [Category.assoc, h2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
          lift_snd, hy]
    rw [Hom.mul_def, Over.comp_left, Category.assoc, hm, ← Category.assoc, this, Over.comp_left, Category.assoc]
  have rone : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left), p ≫ T.hom = T'.hom ≫ f →
      (1 : T' ⟶ A).left ≫ π = p ≫ (toUnit T ≫ e₀).left := by
    intro T' T p hp
    rw [Hom.one_def, Over.comp_left, Category.assoc, he, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (by rw [← hp]; exact Category.assoc _ _ _)
  have rinv : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left) {x' : T' ⟶ A} {x : T ⟶ A₀},
      x'.left ≫ π = p ≫ x.left → (x'⁻¹).left ≫ π = p ≫ (x ≫ i₀).left := by
    intro T' T p x' x hx
    rw [Hom.inv_def, Over.comp_left, Category.assoc, hi, ← Category.assoc, hx, Over.comp_left, Category.assoc]

  have cov : ∀ T : Over S₀, ∃ (T' : Over S) (p : T'.left ⟶ T.left), p ≫ T.hom = T'.hom ≫ f ∧
      (∀ a b : T ⟶ A₀, p ≫ a.left = p ≫ b.left → a = b) ∧
      ∀ x : T ⟶ A₀, ∃ x' : T' ⟶ A, x'.left ≫ π = p ≫ x.left := by
    intro T
    refine ⟨Over.mk (pullback.snd T.hom f), pullback.fst T.hom f, pullback.condition, fun a b h => ?_, fun x => ?_⟩
    · have : Epi (pullback.fst T.hom f) := Flat.epi_of_flat_of_surjective _
      ext1
      exact (cancel_epi (pullback.fst T.hom f)).1 h
    · refine ⟨Over.homMk (hπ.lift (pullback.fst T.hom f ≫ x.left) (pullback.snd T.hom f) ?_) ?_, ?_⟩
      · rw [Category.assoc, Over.w x, pullback.condition]
      · exact hπ.lift_snd _ _ _
      · exact hπ.lift_fst _ _ _
  have one_mul' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift (toUnit T ≫ e₀) x ≫ m₀ = x := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p (rone p hp) hx, _root_.one_mul, hx]
  have mul_one' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift x (toUnit T ≫ e₀) ≫ m₀ = x := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p hx (rone p hp), _root_.mul_one, hx]
  have assoc' : ∀ {T : Over S₀} (x y z : T ⟶ A₀),
      lift (lift x y ≫ m₀) z ≫ m₀ = lift x (lift y z ≫ m₀) ≫ m₀ := by
    intro T x y z
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    obtain ⟨y', hy⟩ := hl y
    obtain ⟨z', hz⟩ := hl z
    apply hinj
    rw [← rmul p (rmul p hx hy) hz, ← rmul p hx (rmul p hy hz), _root_.mul_assoc]
  have linv' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift (x ≫ i₀) x ≫ m₀ = toUnit T ≫ e₀ := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p (rinv p hx) hx, ← rone p hp, inv_mul_cancel]
  have rinv' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift x (x ≫ i₀) ≫ m₀ = toUnit T ≫ e₀ := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p hx (rinv p hx), ← rone p hp, mul_inv_cancel]
  let G : GrpObj A₀ :=
    { one := e₀
      mul := m₀
      one_mul := by
        rw [← one_mul' (λ_ A₀).hom]
        congr 1
      mul_one := by
        rw [← mul_one' (ρ_ A₀).hom]
        congr 1
        apply CartesianMonoidalCategory.hom_ext
        · rw [whiskerLeft_fst, lift_fst, rightUnitor_hom]
        · rw [whiskerLeft_snd, lift_snd]
          congr 1
          exact toUnit_unique _ _
      mul_assoc := by
        have h := assoc' (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) (snd (A₀ ⊗ A₀) A₀)
        have a1 : m₀ ▷ A₀ = lift (lift (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) ≫ m₀)
            (snd (A₀ ⊗ A₀) A₀) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [whiskerRight_fst, lift_fst, ← comp_lift, lift_fst_snd, Category.comp_id]
          · rw [whiskerRight_snd, lift_snd]
        have a2 : (α_ A₀ A₀ A₀).hom ≫ A₀ ◁ m₀ = lift (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀)
            (lift (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) (snd (A₀ ⊗ A₀) A₀) ≫ m₀) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [Category.assoc, whiskerLeft_fst, lift_fst, associator_hom_fst]
          · rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
            congr 1
            apply CartesianMonoidalCategory.hom_ext
            · rw [Category.assoc, lift_fst, associator_hom_snd_fst]
            · rw [Category.assoc, lift_snd, associator_hom_snd_snd]
        rw [← Category.assoc, a2, a1, h]
      inv := i₀
      left_inv := by simpa only [Category.id_comp] using linv' (𝟙 A₀)
      right_inv := by simpa only [Category.id_comp] using rinv' (𝟙 A₀) }
  refine ⟨G, hπ, fun T x y x₀ y₀ hx hy => ?_⟩
  have := rmul (T' := T) (T := Over.mk (T.hom ≫ f)) (𝟙 T.left) (x' := x) (y' := y) (x := x₀) (y := y₀)
    (hx.symm.trans (Category.id_comp _).symm) (hy.symm.trans (Category.id_comp _).symm)
  exact (this.trans (Category.id_comp _)).symm
end GlobalTheory.GrpDescent
