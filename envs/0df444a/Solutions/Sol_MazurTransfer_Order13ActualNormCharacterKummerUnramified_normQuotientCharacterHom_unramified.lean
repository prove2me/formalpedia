-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormCharacterKummerUnramified.normQuotientCharacterHom_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T07:23:03.729475+00:00
-- url     : https://prove2.me/submissions/240e8554-3e20-4ce6-908e-03eaacd3ea81

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: push the existing actual norm Kummer homomorphism through
an actual coefficient intertwiner and retain its genuine good-prime inertia
vanishing. Named downstream consumer: the two ordered character Selmer images.
This coefficient pushforward carries no assertion of injectivity.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerPushforwardData
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerUnramified_pushed_norm_class_unramified
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
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance goodPrimeNormQuotientCharacterHomUnramifiedSourceProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualNormCharacterContinuousH1
variable (hsurj : Function.Surjective (normHom K φ))

variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
variable (A : ValuationSubring K) (hA : A.LiesOverPrime q)
include hq hne hφ hA

theorem solution (x : NormQuotient φ) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  rw [normQuotientCharacterHom_apply]
  exact MazurTransfer.Order13ActualNormCharacterKummerUnramified.pushed_norm_class_unramified K φ τ f q hq hne hφ A hA a
    (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)

#print axioms solution
