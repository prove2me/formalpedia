-- Prove2me | solution 1 for MazurTransfer.original_actual_integral_character_quotients
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T18:30:10.788608+00:00
-- url     : https://prove2.me/submissions/fa57ec99-5502-4a49-954c-8ba99aa1437d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the previously selected pi and conjugate-pi character maps on a single same finite-flat source Hopf model carrying its entire original integral point functor and actual arithmetic kernel labels.
Named downstream consumer: actual nineteen character Kummer unit conditions and integral norm torsor pushforwards.
-/
import Definitions.Def_MazurTransfer_OriginalActualIntegralCharacterQuotientsData20261020
import Definitions.Def_MazurTransfer_OriginalActualIntegralArithmeticKernelHopfModelsData20261020
import Theorems.Thm_MazurTransfer_original_integral_representation_quotient
import Theorems.Thm_MazurTransfer_original_actual_integral_arithmetic_kernel_hopf_models
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open MazurTransfer.Order13ActualPicardSchemeNormGroupHom MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison MazurTransfer.Order13ActualPicardNormKernelGaloisAction
open MazurTransfer.Order13ActualArithmeticKernelAdditiveAction MazurTransfer.Order13ActualNormKernelF19Representation
open MazurTransfer.Order13ActualNormKernelFiniteModule MazurTransfer.Order13IntegralRepresentationQuotient
open MazurTransfer.Order13ActualIntegralArithmeticKernelHopfModels
open scoped CategoryTheory.MonObj
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.Order13ActualOrderedCharacterContinuousH1
open MazurTransfer.Order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsFiniteLeftSchemeSchemePi_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactPrimeOfNatNat_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualIntegralCharacterQuotients
attribute [local instance] MazurTransfer.Order13ActualIntegralCharacterQuotients.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualIntegralCharacterQuotients
namespace MazurTransfer.OriginalActualIntegralCharacterQuotientsBoundary20261020
end MazurTransfer.OriginalActualIntegralCharacterQuotientsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: integral finite-flat quotients for the PREVIOUSLY SELECTED
pi and conjugate-pi character maps, preserving a single source Hopf algebra,
its all-algebra integral points and its actual arithmetic kernel labels.
Named downstream consumer: actual nineteen character Kummer unit conditions.
-/

noncomputable section
namespace MazurTransfer.OriginalActualIntegralCharacterQuotientsProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13IntegralArithmeticNormKernelComparison Order13ActualPicardNormKernelGaloisAction
open Order13ActualArithmeticKernelAdditiveAction Order13ActualNormKernelF19Representation
open Order13ActualNormKernelFiniteModule Order13IntegralRepresentationQuotient
open Order13ActualIntegralArithmeticKernelHopfModels
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]


variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]



variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (ρ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (p : Representation.IntertwiningMap (kernelRepresentation K φ) ρ)



theorem coherent_integral_character_quotient
    (hmodel : HasArithmeticIntegralKernelHopfModel q hq K φ)
    (hp : Function.Surjective p) :
    HasCoherentIntegralCharacterQuotient q hq K φ ρ p := by
  obtain ⟨G, iCR, iHA, hFin, hFree, hComm, eAll, hMul, hNat, e, he_add, he_act, hCompat⟩ := hmodel
  letI := iCR
  letI := iHA
  letI := hFin
  letI := hFree
  letI := hComm
  exact ⟨G, iCR, iHA, hFin, hFree, hComm, eAll, hMul, hNat, e, he_add, he_act, hCompat,
    MazurTransfer.original_integral_representation_quotient q K φ ρ p hp G e he_add he_act⟩







open NineteenRootsGaloisRepresentation Order13ActualOrderedCharacterContinuousH1

variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

include hq in
theorem actual_integral_selected_character_quotients :
    HasCoherentIntegralCharacterQuotient q hq K schemePi (rootsRepresentation K)
      (piQuotient K z hz 𝒱) ∧
    HasCoherentIntegralCharacterQuotient q hq K schemePiConjugate
      (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱) := by
  have hmodels := (MazurTransfer.original_actual_integral_arithmetic_kernel_hopf_models).2.1 q hq K
  exact ⟨coherent_integral_character_quotient q hq K schemePi (rootsRepresentation K)
      (piQuotient K z hz 𝒱) hmodels.1 (piQuotient_surjective K z hz 𝒱),
    coherent_integral_character_quotient q hq K schemePiConjugate
      (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱)
      hmodels.2 (piConjugateQuotient_surjective K z hz 𝒱)⟩


theorem actual_nineteen_selected_character_quotients
    (F : Type) [Field F] [CharZero F] [IsGalois ℚ F] [IsAlgClosed F]
    [Algebra (LocalRing 19) F] [IsScalarTower (LocalRing 19) ℚ F]
    (w : F) (hw : IsPrimitiveRoot w 13) (𝒲 : (curveScheme ℚ).TwoAffineOpenCover) :
    HasCoherentIntegralCharacterQuotient 19 MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good
      F schemePi (rootsRepresentation F) (piQuotient F w hw 𝒲) ∧
    HasCoherentIntegralCharacterQuotient 19 MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good
      F schemePiConjugate (twistedRootsRepresentation F w hw) (piConjugateQuotient F w hw 𝒲) :=
  actual_integral_selected_character_quotients 19
    MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good F w hw 𝒲

end MazurTransfer.OriginalActualIntegralCharacterQuotientsProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (ρ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (p : Representation.IntertwiningMap (kernelRepresentation K φ) ρ), ∀ (hmodel : HasArithmeticIntegralKernelHopfModel q hq K φ)
    (hp : Function.Surjective p),
HasCoherentIntegralCharacterQuotient q hq K φ ρ p) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover), HasCoherentIntegralCharacterQuotient q hq K schemePi (rootsRepresentation K)
      (piQuotient K z hz 𝒱) ∧
    HasCoherentIntegralCharacterQuotient q hq K schemePiConjugate
      (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱)) ∧ (∀ (F : Type) [Field F] [CharZero F] [IsGalois ℚ F] [IsAlgClosed F]
    [Algebra (LocalRing 19) F] [IsScalarTower (LocalRing 19) ℚ F]
    (w : F) (hw : IsPrimitiveRoot w 13) (𝒲 : (curveScheme ℚ).TwoAffineOpenCover),
HasCoherentIntegralCharacterQuotient 19 MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good
      F schemePi (rootsRepresentation F) (piQuotient F w hw 𝒲) ∧
    HasCoherentIntegralCharacterQuotient 19 MazurTransfer.Order13ExceptionalNineteenFlatNormFibres.nineteen_good
      F schemePiConjugate (twistedRootsRepresentation F w hw) (piConjugateQuotient F w hw 𝒲)) := by
  exact ⟨MazurTransfer.OriginalActualIntegralCharacterQuotientsProof20261020.coherent_integral_character_quotient, MazurTransfer.OriginalActualIntegralCharacterQuotientsProof20261020.actual_integral_selected_character_quotients, MazurTransfer.OriginalActualIntegralCharacterQuotientsProof20261020.actual_nineteen_selected_character_quotients⟩
#print axioms solution
