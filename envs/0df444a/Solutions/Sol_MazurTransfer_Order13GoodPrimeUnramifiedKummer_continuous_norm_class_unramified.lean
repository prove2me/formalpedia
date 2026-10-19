-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeUnramifiedKummer.continuous_norm_class_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T06:50:06.694989+00:00
-- url     : https://prove2.me/submissions/bd888d4d-fa28-4f15-bac7-c5fa76cd44eb

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous Kummer classes for the SAME actual rational
norm maps restrict to zero on the genuine valuation inertia groups at
every prime outside two, thirteen and nineteen.
Named downstream consumer: global norm Selmer bounds.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestriction_restrictedClass_zero_iff_subgroup_invariant_preimage
import Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_norm_lift_inertia_fixed
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13LocalIntegralCoefficientMaps
open scoped CategoryTheory.MonObj
local instance goodPrimeUnramifiedKummerOriginalProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  Order13SameIntegralPicardRationalSchemeComparison.actualGroup
local instance goodPrimeUnramifiedKummerOriginalProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj

variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
include hq hne

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable [IsGalois ℚ K]
local instance goodPrimeUnramifiedKummerOriginalProvider320261018 : TopologicalSpace (Points K) := (⊥ : TopologicalSpace (Points K))
local instance goodPrimeUnramifiedKummerOriginalProvider420261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance goodPrimeUnramifiedKummerOriginalProvider520261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance goodPrimeUnramifiedKummerOriginalProvider620261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
open Order13ActualPicardNormAlgebraicCohomology Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance goodPrimeUnramifiedKummerOriginalProvider720261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormSubgroupRestriction

theorem solution
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0 := by
  apply (MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictedClass_zero_iff_subgroup_invariant_preimage K φ
    (A.inertiaSubgroupIn ℚ) a b hb).mpr
  exact ⟨b, hb, fun σ => MazurTransfer.Order13GoodPrimeUnramifiedKummer.norm_lift_inertia_fixed q hq hne K φ hφ A hA a b hb σ.val σ.property⟩

#print axioms solution
