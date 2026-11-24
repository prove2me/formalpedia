-- Prove2me | solution 1 for GlobalTheory.finite_of_isIntegral_of_birational_of_finite_over_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:07.931015+00:00
-- url     : https://prove2.me/submissions/244f7d26-73d0-417f-a493-3451e4d6c08d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FiniteOfIsIntegralOfBirationalOfPresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (R A B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CharZero R] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (hb : ∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) :
    Module.Finite A B := by
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let L := FractionRing B
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply A B L]; rfl
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A B L]; exact hBL.comp hAB

  haveI : IsFractionRing A L := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro y
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ hAL).mpr (nonZeroDivisors.ne_zero y.2))
    · intro z
      obtain ⟨⟨x, y⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors B) z
      obtain ⟨a₁, c₁, hc₁, h₁⟩ := hb x
      obtain ⟨a₂, c₂, hc₂, h₂⟩ := hb (y : B)
      have hy : (y : B) ≠ 0 := nonZeroDivisors.ne_zero y.2
      have ha₂ : a₂ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h₂
        exact mul_ne_zero ((map_ne_zero_iff _ hAB).mpr hc₂) hy h₂
      refine ⟨⟨a₁ * c₂, ⟨c₁ * a₂, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hc₁ ha₂)⟩⟩, ?_⟩
      simp only [IsScalarTower.algebraMap_apply A B L, map_mul, ← h₁, ← h₂]
      simp only [map_mul] at hz ⊢
      rw [← hz]; ring
    · intro x y hxy
      exact ⟨1, by rw [hAL hxy]⟩
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr (by
    rw [IsScalarTower.algebraMap_eq R A L]
    exact hAL.comp (FaithfulSMul.algebraMap_injective R A))
  let K := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.trans A
  let f : B →ₐ[R] integralClosure R L :=
    (IsScalarTower.toAlgHom R B L).codRestrict (integralClosure R L)
      (fun b => (Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R B L))
  have hf : Function.Injective f.toLinearMap := fun x y h =>
    hBL (congrArg Subtype.val h)
  haveI : IsNoetherian R (integralClosure R L) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian R B := isNoetherian_of_injective f.toLinearMap hf
  haveI : Module.Finite R B := Module.IsNoetherian.finite R B
  exact Module.Finite.of_restrictScalars_finite R A B
end GlobalTheory
