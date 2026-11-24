-- Prove2me | solution 1 for GlobalTheory.DivisibleHom.isMonHom_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:46.751795+00:00
-- url     : https://prove2.me/submissions/d720bfdf-2015-4880-91cc-a5450062986e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
import Theorems.Thm_GlobalTheory_DivisibleHom_cancel_of_flat_surjective
import Theorems.Thm_GlobalTheory_DivisibleHom_exists_lift_point
import Theorems.Thm_GlobalTheory_DivisibleHom_isMonHom_of_mul_points
import Theorems.Thm_GlobalTheory_DivisibleHom_comp_mulA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.DivisibleHom
namespace _root_.GlobalTheory.DivisibleHom
theorem _root_.solution {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    (M : ℕ) [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (φ : A ⟶ B) [IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ)] : IsMonHom φ := by
  have hmm : ∀ (T : Over S) (a b : T ⟶ A),
      (a * b) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M = (a ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) * (b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) := by
    intro T a b
    simp only [_root_.GlobalTheory.DivisibleHom.comp_mulA, mul_pow]
  apply _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points
  intro T x y
  obtain ⟨T₁, e₁, x', he₁, hs₁, hx'⟩ := _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) x
  haveI := he₁
  haveI := hs₁
  obtain ⟨T₂, e₂, y', he₂, hs₂, hy'⟩ :=
    _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) (e₁ ≫ y)
  haveI := he₂
  haveI := hs₂
  haveI : Flat (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  haveI : Surjective (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  have hxe : (e₂ ≫ e₁) ≫ x = (e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hx', Category.assoc]
  have hye : (e₂ ≫ e₁) ≫ y = y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hy']
  apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (e₂ ≫ e₁)
  calc (e₂ ≫ e₁) ≫ (x * y) ≫ φ = (((e₂ ≫ e₁) ≫ x) * ((e₂ ≫ e₁) ≫ y)) ≫ φ := by
        rw [← Category.assoc (e₂ ≫ e₁), comp_mul]
    _ = (((e₂ ≫ x') * y') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) ≫ φ := by rw [hxe, hye, hmm]
    _ = ((e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) * (y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) := by
        rw [Category.assoc, mul_comp]
    _ = (e₂ ≫ e₁) ≫ ((x ≫ φ) * (y ≫ φ)) := by
        rw [comp_mul, ← Category.assoc (e₂ ≫ e₁) x, ← Category.assoc (e₂ ≫ e₁) y, hxe, hye]
        simp only [Category.assoc]
end _root_.GlobalTheory.DivisibleHom
end GlobalTheory.DivisibleHom
