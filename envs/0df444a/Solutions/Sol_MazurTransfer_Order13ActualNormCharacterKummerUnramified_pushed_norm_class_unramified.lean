-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormCharacterKummerUnramified.pushed_norm_class_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T06:57:46.270908+00:00
-- url     : https://prove2.me/submissions/1e9e2a12-4bdc-4308-ad10-97214a5e37d1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: push the existing actual norm Kummer homomorphism through
an actual coefficient intertwiner and retain its genuine good-prime inertia
vanishing. Named downstream consumer: the two ordered character Selmer images.
This coefficient pushforward carries no assertion of injectivity.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerPushforwardData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_continuous_norm_class_unramified
noncomputable section
open MazurTransfer
open MazurTransfer.Order13ActualNormCharacterKummerUnramified
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance goodPrimeCharacterKummerUnramifiedSourceProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance goodPrimeCharacterKummerUnramifiedSourceProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance goodPrimeCharacterKummerUnramifiedSourceProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance goodPrimeCharacterKummerUnramifiedSourceProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance goodPrimeCharacterKummerUnramifiedSourceProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance goodPrimeCharacterKummerUnramifiedSourceProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance goodPrimeCharacterKummerUnramifiedSourceProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance goodPrimeCharacterKummerUnramifiedSourceProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance goodPrimeCharacterKummerUnramifiedSourceProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance goodPrimeCharacterKummerUnramifiedSourceProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance goodPrimeCharacterKummerUnramifiedSourceProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance goodPrimeCharacterKummerUnramifiedSourceProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualNormCharacterContinuousH1
variable (hsurj : Function.Surjective (normHom K φ))

open Order13LocalIntegralCoefficientMaps
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
variable (A : ValuationSubring K) (hA : A.LiesOverPrime q)
include hq hne hφ hA

theorem solution
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0 := by
  apply MazurTransfer.Order13ActualNormCharacterContinuousH1.restriction_zero_of_source_zero
  exact Order13GoodPrimeUnramifiedKummer.continuous_norm_class_unramified
    q hq hne K φ hφ A hA a b hb

#print axioms solution
