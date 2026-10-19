-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelGoodPrimeInertia.kernel_inertia_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T01:22:02.267099+00:00
-- url     : https://prove2.me/submissions/e0ce82f1-8feb-440f-89fa-958c33f4f9cd

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: genuine good-prime valuation inertia acts trivially on
the actual norm kernels, without assuming their geometric degrees.
Named downstream consumer: Galois kernel representations and Selmer bounds. -/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_norm_lift_inertia_fixed
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13LocalIntegralCoefficientMaps
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup
attribute [local instance] MazurTransfer.Order13ActualPicardNormKummerCocycles.actualPicardNormKummerDataProvider220261017


open Order13ActualPicardNormKernelGaloisAction
local instance sourceGoodPrimeKernelActionProvider20261019 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
namespace MazurTransfer.ActualNormKernelGoodPrimeInertiaProofHelpers20261019
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance : IsMonHom schemePi := schemePi_isMonHom
local instance : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]


open Order13ActualPicardNormKernelGaloisAction
local instance : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
include hq hne

theorem kernel_inertia_fixed (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (z : Kernel K φ) :
    σ • z = z := by
  have hr : rationalPoint K (1 : RationalPoints) = 1 := MonObj.comp_one _
  have hz : z.val ≫ φ = rationalPoint K (1 : RationalPoints) := z.property.trans hr.symm
  apply Subtype.ext
  exact Order13GoodPrimeUnramifiedKummer.norm_lift_inertia_fixed q hq hne K φ
    hφ A hA 1 z.val hz σ hσ

end MazurTransfer.ActualNormKernelGoodPrimeInertiaProofHelpers20261019

theorem solution (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (z : Kernel K φ) :
    σ • z = z := by
  exact MazurTransfer.ActualNormKernelGoodPrimeInertiaProofHelpers20261019.kernel_inertia_fixed K φ q hq hne hφ A hA σ hσ z
#print axioms solution
