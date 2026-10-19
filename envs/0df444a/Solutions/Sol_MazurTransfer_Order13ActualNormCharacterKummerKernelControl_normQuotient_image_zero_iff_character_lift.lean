-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormCharacterKummerKernelControl.normQuotient_image_zero_iff_character_lift
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T02:51:32.724183+00:00
-- url     : https://prove2.me/submissions/2954f8e6-1922-4094-ba7b-2e3202363493

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
local instance actualNormCharacterKummerZeroCriterionProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormCharacterKummerZeroCriterionProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormCharacterKummerZeroCriterionProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormCharacterKummerZeroCriterionProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormCharacterKummerZeroCriterionProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormCharacterKummerZeroCriterionProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormCharacterKummerZeroCriterionProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormCharacterKummerZeroCriterionProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualNormCharacterKummerZeroCriterionProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormCharacterKummerZeroCriterionProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance actualNormCharacterKummerZeroCriterionProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance actualNormCharacterKummerZeroCriterionProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance actualNormCharacterKummerZeroCriterionProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
variable (hsurj : Function.Surjective (normHom K φ))

theorem solution
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) (x : NormQuotient φ) :
    normQuotientCharacterHom K φ τ p hsurj x = 1 ↔
    ∃ y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ),
      inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd := by
  change (continuousQuotientHom K φ hsurj x).toAdd ∈ LinearMap.ker (mapClass K φ τ p) ↔ _
  rw [← range_inclusionClass_eq_ker_mapClass K φ σ τ i p hi hp hk]
  rfl

#print axioms solution
