-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormCharacterKummerKernelControl.hasExactCharacterKummerSequence_of_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T03:15:43.362085+00:00
-- url     : https://prove2.me/submissions/5a6742e4-4a40-42a8-a86e-d5de1b0dbf65

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernel of an actual norm-character Kummer pushforward
is exactly the original norm Kummer classes lifted from the character-line
continuous H1. Named downstream consumer: actual norm Selmer kernel bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1GlobalExactnessBridgeData
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerPushforwardData

noncomputable section
open MazurTransfer
open MazurTransfer.Order13ActualNormCharacterKummerKernelControl
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormCharacterKummerExactSequenceProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterKummerExactSequenceProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterKummerExactSequenceProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterKummerExactSequenceProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormCharacterKummerExactSequenceProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterKummerExactSequenceProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterKummerExactSequenceProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterKummerExactSequenceProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormCharacterKummerExactSequenceProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormCharacterKummerExactSequenceProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormCharacterKummerExactSequenceProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualNormCharacterKummerExactSequenceProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance actualNormCharacterKummerExactSequenceProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
variable (hsurj : Function.Surjective (normHom K φ))

theorem solution
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasExactCharacterKummerSequence K φ σ τ hsurj := by
  refine ⟨i, p, hi, hp, hk, range_inclusionClass_eq_ker_mapClass K φ σ τ i p hi hp hk, ?_⟩
  intro x
  change (continuousQuotientHom K φ hsurj x).toAdd ∈ LinearMap.ker (mapClass K φ τ p) ↔ _
  rw [← range_inclusionClass_eq_ker_mapClass K φ σ τ i p hi hp hk]
  rfl

#print axioms solution
