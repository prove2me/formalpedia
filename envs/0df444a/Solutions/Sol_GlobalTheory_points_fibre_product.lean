-- Prove2me | solution 1 for GlobalTheory.points_fibre_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:40:38.016272+00:00
-- url     : https://prove2.me/submissions/c4ab362d-2a43-4a0e-9ab6-14f07a314f84

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsFibreProduct
import Theorems.Thm_GlobalTheory_bxFibre_unique
import Theorems.Thm_GlobalTheory_bxFibre_exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀))) {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R) (f₂ : LHom R₂ R),
    IsFibreSq p₁ p₂ f₁ f₂ → ∀ (a : sp (R₀ := R₀) (R₁ : Type) ⟶ X) (b : sp (R₀ := R₀) (R₂ : Type) ⟶ X), spMap f₁.1 ≫ a = spMap f₂.1 ≫ b →
    ∃! c : sp (R₀ := R₀) (F : Type) ⟶ X, spMap p₁.1 ≫ c = a ∧ spMap p₂.1 ≫ c = b) := by
  intro R₀ _ X F R₁ R₂ R p₁ p₂ f₁ f₂ hsq a b hab
  obtain ⟨hc, -, -, hex⟩ := hsq
  haveI : IsLocalHom p₁.1.toRingHom := p₁.2
  haveI : IsLocalHom f₁.1.toRingHom := f₁.2
  haveI : IsLocalHom f₂.1.toRingHom := f₂.2
  have hinj : ∀ s t, p₁.1.toRingHom s = p₁.1.toRingHom t → p₂.1.toRingHom s = p₂.1.toRingHom t →
      s = t := fun s t h1 h2 =>
    (hex (p₁.1 t) (p₂.1 t) (AlgHom.congr_fun hc t)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  obtain ⟨c, h1, h2⟩ := bxFibre_exists (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom
    f₁.1.toRingHom f₂.1.toRingHom hex hinj a.left b.left (congrArg (·.left) hab)
  have hw : c ≫ X.hom = (sp (R₀ := R₀) (F : Type)).hom := by
    refine bxFibre_unique p₁.1.toRingHom p₂.1.toRingHom hinj _ _ ?_ ?_
    · rw [← Category.assoc, h1]
      exact (Over.w a).trans (Over.w (spMap p₁.1)).symm
    · rw [← Category.assoc, h2]
      exact (Over.w b).trans (Over.w (spMap p₂.1)).symm
  refine ⟨Over.homMk c hw, ⟨Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩, ?_⟩
  rintro c' ⟨k1, k2⟩
  apply Over.OverMorphism.ext
  exact bxFibre_unique (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom hinj _ _
    ((congrArg (·.left) k1).trans h1.symm) ((congrArg (·.left) k2).trans h2.symm)
end GlobalTheory
