-- Prove2me | solution 1 for MazurTransfer.original_exceptional_nineteen_norm_model_properties
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T05:50:29.616344+00:00
-- url     : https://prove2.me/submissions/5c0e10f2-af86-4d34-9927-a6f03c21d27b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the same actual integral Picard at nineteen, the same generic point and its unique integral extension, and the same two finite-flat norm-preimage families.
Named downstream consumer: actual arithmetic integral norm-kernel Hopf models and Kummer local conditions at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalExceptionalNineteenNormModelData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_original_integral_norms_finite_flat_all_good_primes
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13GoodPrimeLocalPicardModels MazurTransfer.Order13GoodPrimeIntegralNormExtensions
open MazurTransfer.Order13GoodPrimeLocalGenericPicardComparison MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ExceptionalNineteenFlatNormFibres
attribute [local instance] MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.instFactPrimeOfNatNat_order13ExceptionalNineteenFlatNormFibres
namespace MazurTransfer.OriginalExceptionalNineteenNormModelBoundary20261020
end MazurTransfer.OriginalExceptionalNineteenNormModelBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: specialize the SAME actual Picard norm extensions to
Z_(19); extend each generic point uniquely and retain finite-flat,
locally finitely presented, surjective norm preimage families.
Named downstream consumer: exceptional nineteen local Kummer classes.
This proves flat norm models, without asserting a character unit bound.
-/

noncomputable section
namespace MazurTransfer.OriginalExceptionalNineteenNormModelProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeLocalGenericPicardComparison Order13LocalIntegralCoefficientMaps
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ExceptionalNineteenFlatNormFibres










theorem actual_generic_point_has_unique_integral_extension
    (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase) :
    ∃! x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) integralModel.toBase,
      genericFibreRestrict (LocalRing 19) ℚ integralModel.toBase
        (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) x = actualGenericPoint z := by
  exact (localPicard_neron 19 nineteen_good).existsUnique_extension inferInstance
    (actualGenericPoint z)

theorem actual_nineteen_norm_fibres_finite_flat {T : Scheme}
    (x : T ⟶ integralModel.P) :
    (IsFinite (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      Flat (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      Surjective (pullback.snd (integralPi 19 nineteen_good).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      Flat (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      Surjective (pullback.snd (integralPiConjugate 19 nineteen_good).val x)) :=
  (MazurTransfer.original_integral_norms_finite_flat_all_good_primes).2 19 nineteen_good x

end MazurTransfer.OriginalExceptionalNineteenNormModelProof20261020

theorem solution : (¬ (19 : ℤ) ∣ 104) ∧ (∀ (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase),
∃! x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) integralModel.toBase,
      genericFibreRestrict (LocalRing 19) ℚ integralModel.toBase
        (𝟙 (Spec (CommRingCat.of (LocalRing 19)))) x = actualGenericPoint z) ∧ (∀ {T : Scheme}
    (x : T ⟶ integralModel.P),
(IsFinite (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      Flat (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPi 19 nineteen_good).val x) ∧
      Surjective (pullback.snd (integralPi 19 nineteen_good).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      Flat (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      LocallyOfFinitePresentation (pullback.snd (integralPiConjugate 19 nineteen_good).val x) ∧
      Surjective (pullback.snd (integralPiConjugate 19 nineteen_good).val x))) := by
  exact ⟨MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good, MazurTransfer.OriginalExceptionalNineteenNormModelProof20261020.actual_generic_point_has_unique_integral_extension, MazurTransfer.OriginalExceptionalNineteenNormModelProof20261020.actual_nineteen_norm_fibres_finite_flat⟩
#print axioms solution
