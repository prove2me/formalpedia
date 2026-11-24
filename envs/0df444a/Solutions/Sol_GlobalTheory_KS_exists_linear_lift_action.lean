-- Prove2me | solution 1 for GlobalTheory.KS.exists_linear_lift_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:10:21.657872+00:00
-- url     : https://prove2.me/submissions/2a76a09a-1c22-4ce4-ab53-e59fb90c2bcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfLineSubsetDiscrete
import Theorems.Thm_GlobalTheory_KS_linear_eq_of_ex_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (∀ (f : P₀.A ⟶ P₀.A) (F F' : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f) → F = F') ∧ ∀ (O : Type) [CommRing O] (act : OAct O P₀.A), ∃ F : O →+* Module.End ℂ (Fin P₀.g → ℂ), ∀ a z, u.ex (F a z) = u.ex z ≫ act.act a := by
  intro P₀ u Hm χ hu
  refine ⟨fun f F F' h h' => linear_eq_of_ex_eq u F F' fun z => (h z).trans (h' z).symm, ?_⟩
  intro O _ act
  choose F hF using fun a => hu.endo (act.act a) (act.hom a)
  have hone : F 1 = (1 : Module.End ℂ (Fin P₀.g → ℂ)) :=
    linear_eq_of_ex_eq u _ _ fun z => by rw [hF, act.one, Category.comp_id]; rfl
  have hmul : ∀ a b, F (a * b) = (F a : Module.End ℂ (Fin P₀.g → ℂ)) * F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, mul_comm a b, act.mul, Module.End.mul_apply, hF, hF, Category.assoc]
  have hadd : ∀ a b, F (a + b) = F a + F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, act.add, LinearMap.add_apply, u.ex_add, hF, hF, MonObj.comp_mul]
  exact ⟨RingHom.mk' ⟨⟨F, hone⟩, hmul⟩ hadd, hF⟩
end GlobalTheory.KS
