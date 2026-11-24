-- Prove2me | solution 1 for GlobalTheory.DivisibleHom.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:52.432656+00:00
-- url     : https://prove2.me/submissions/d0133186-b30c-40ce-9ed8-8d7078f4c26a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne
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
theorem _root_.solution {A B : Over S} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] (M : ℕ)
    [QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (u : A ⟶ B) [IsMonHom u] (hu : ∀ (T : Over S) (x : T ⟶ A), x ^ M = 1 → x ≫ u = 1) :
    ∃ φ : A ⟶ B, _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ = u := by
  have key : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left),
      g₁ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left = g₂ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left → g₁ ≫ u.left = g₂ ≫ u.left := by
    intro Z g₁ g₂ hg
    have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
      rw [← Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M), ← Category.assoc, ← hg, Category.assoc]
    let x₁ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₁ rfl
    let x₂ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₂ hw
    have hx : x₁ ^ M = x₂ ^ M := by
      rw [← _root_.GlobalTheory.DivisibleHom.comp_mulA, ← _root_.GlobalTheory.DivisibleHom.comp_mulA]
      ext1
      simpa [x₁, x₂] using hg
    have h1 : (x₁ * x₂⁻¹) ^ M = 1 := by rw [mul_pow, inv_pow, hx, mul_inv_cancel]
    have h3 : IsMonHom.monoidHom u _ (x₁ * x₂⁻¹) = 1 := hu _ _ h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    simpa [x₁, x₂] using congrArg CommaMorphism.left h3
  refine ⟨Over.homMk (EffectiveEpi.desc _ _ key) ?_, ?_⟩
  · rw [← cancel_epi (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left, ← Category.assoc, EffectiveEpi.fac, Over.w u,
      Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M)]
  · ext1
    simp [EffectiveEpi.fac]
end _root_.GlobalTheory.DivisibleHom
end GlobalTheory.DivisibleHom
