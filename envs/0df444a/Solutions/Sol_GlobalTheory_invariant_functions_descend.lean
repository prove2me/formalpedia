-- Prove2me | solution 1 for GlobalTheory.invariant_functions_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:01:37.015884+00:00
-- url     : https://prove2.me/submissions/fc13ee48-6079-4256-86cc-389bca9d065c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Theorems.Thm_GlobalTheory_FunDescent_app_injective
import Theorems.Thm_GlobalTheory_FunDescent_isUnit_of_isUnit_app
import Theorems.Thm_GlobalTheory_FunDescent_exists_app_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (U : B.left.Opens), Function.Injective (q.left.app U).hom ∧ (∀ a : Γ(B.left, U), IsUnit ((q.left.app U).hom a) → IsUnit a) ∧ ∀ f : Γ(G.left, q.left ⁻¹ᵁ U), (∀ (Z : Over S) (t : Z ⟶ T) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ U)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ U)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom f = (g.left.appLE _ ⊤ h₂).hom f) → ∃ a : Γ(B.left, U), (q.left.app U).hom a = f := by
  intro S G B T _ _ _ q i hq hi _ _ _ hP U
  refine ⟨FunDescent.app_injective _ U, FunDescent.isUnit_of_isUnit_app _ U, fun f hf => ?_⟩
  refine FunDescent.exists_app_eq q.left U f fun Z g₁ g₂ h₁ h₂ e => ?_
  let Z' : Over S := Over.mk (g₂ ≫ G.hom)
  let k₂ : Z' ⟶ G := Over.homMk g₂ rfl
  let k₁ : Z' ⟶ G := Over.homMk g₁ (by
    change g₁ ≫ G.hom = g₂ ≫ G.hom
    rw [← Over.w q, reassoc_of% e])
  have e' : k₁ ≫ q = k₂ ≫ q := Over.OverMorphism.ext e
  have w : (k₁ * k₂⁻¹) ≫ q = toUnit Z' ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
    rfl
  have ht : (hP.lift _ _ w ≫ i) * k₂ = k₁ := by
    rw [hP.lift_fst, inv_mul_cancel_right]
  have := hf Z' (hP.lift _ _ w) k₂
  rw [ht] at this
  exact this h₁ h₂
end GlobalTheory
