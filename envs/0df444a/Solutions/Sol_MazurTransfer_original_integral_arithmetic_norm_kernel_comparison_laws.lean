-- Prove2me | solution 1 for MazurTransfer.original_integral_arithmetic_norm_kernel_comparison_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T03:26:56.57992+00:00
-- url     : https://prove2.me/submissions/f8b9ccbe-e6df-4c1a-8dc9-3bd49b21ceaa

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the same integral norm-kernel point functor with the previously fixed arithmetic kernel, preserving its multiplication and existing Galois spectrum-precomposition action.
Named downstream consumer: actual finite-flat ordered arithmetic character quotients.
-/
import Definitions.Def_MazurTransfer_OriginalIntegralArithmeticNormKernelComparisonData20261020
import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison MazurTransfer.Order13IntegralArithmeticFieldPointComparison
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardGeometricNormPreimages MazurTransfer.Order13ActualPicardNormKummerCocycles
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13IntegralArithmeticNormKernelComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticNormKernelComparison
attribute [local instance] MazurTransfer.Order13IntegralArithmeticNormKernelComparison.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralArithmeticNormKernelComparison
namespace MazurTransfer.OriginalIntegralArithmeticNormKernelComparisonBoundary20261020
end MazurTransfer.OriginalIntegralArithmeticNormKernelComparisonBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the SAME integral norm-kernel point functor
with the PREVIOUSLY FIXED arithmetic Kernel of the rational norm map.
Preserve its multiplication and the existing Galois action by spectrum
precomposition; no transported substitute action or splitting is used.
Named downstream consumer: finite-flat ordered arithmetic character quotients.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralArithmeticNormKernelComparisonProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralArithmeticFieldPointComparison
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]

variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]




theorem kernelPointEquiv_mul (z w : Kernel K φ) :
    (kernelPointEquiv q hq K φ (z * w)).val =
      (localLaw q hq).mul (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)
        (kernelPointEquiv q hq K φ z).val (kernelPointEquiv q hq K φ w).val :=
  (MazurTransfer.original_integral_arithmetic_field_point_comparison_laws).2.2.1 q hq K z.val w.val

theorem kernelPointEquiv_act (σ : K ≃ₐ[ℚ] K) (z : Kernel K φ) :
    (kernelPointEquiv q hq K φ (σ • z)).val =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Over.w (FieldAutomorphismOverPointAction.fieldAut (LocalRing q) K (σ.restrictScalars (LocalRing q)))) (kernelPointEquiv q hq K φ z).val :=
  (MazurTransfer.original_integral_arithmetic_field_point_comparison_laws).2.2.2.2.2 q hq K σ z.val

end MazurTransfer.OriginalIntegralArithmeticNormKernelComparisonProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (z w : Kernel K φ),
(kernelPointEquiv q hq K φ (z * w)).val =
      (localLaw q hq).mul (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)
        (kernelPointEquiv q hq K φ z).val (kernelPointEquiv q hq K φ w).val) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (σ : K ≃ₐ[ℚ] K) (z : Kernel K φ),
(kernelPointEquiv q hq K φ (σ • z)).val =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Over.w (FieldAutomorphismOverPointAction.fieldAut (LocalRing q) K (σ.restrictScalars (LocalRing q)))) (kernelPointEquiv q hq K φ z).val) := by
  exact ⟨MazurTransfer.OriginalIntegralArithmeticNormKernelComparisonProof20261020.kernelPointEquiv_mul, MazurTransfer.OriginalIntegralArithmeticNormKernelComparisonProof20261020.kernelPointEquiv_act⟩
#print axioms solution
