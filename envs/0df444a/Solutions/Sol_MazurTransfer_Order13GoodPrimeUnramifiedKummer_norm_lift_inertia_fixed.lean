-- Prove2me | solution 1 for MazurTransfer.Order13GoodPrimeUnramifiedKummer.norm_lift_inertia_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T06:35:51.669749+00:00
-- url     : https://prove2.me/submissions/afbed628-0519-434d-a7e7-75290cc0d375

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous Kummer classes for the SAME actual rational
norm maps restrict to zero on the genuine valuation inertia groups at
every prime outside two, thirteen and nineteen.
Named downstream consumer: global norm Selmer bounds.
-/
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeActualNormInertia_actual_norm_lift_of_rational_point_inertia_fixed
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
local instance normLiftInertiaOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  Order13SameIntegralPicardRationalSchemeComparison.actualGroup
local instance normLiftInertiaOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
theorem solution (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
    (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    actionHom K σ b = b := by
  letI : Algebra (LocalRing q) K :=
    ((algebraMap ℚ K).comp (algebraMap (LocalRing q) ℚ)).toAlgebra
  letI : IsScalarTower (LocalRing q) ℚ K :=
    IsScalarTower.of_algebraMap_eq' (R := LocalRing q) (S := ℚ) (A := K) rfl
  have hb' : b.left ≫ φ.left =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) ≫ a.left :=
    congrArg (fun z => z.left) hb
  have h := Order13GoodPrimeActualNormInertia.actual_norm_lift_of_rational_point_inertia_fixed
    q hq hne φ hφ A hA σ hσ ⟨b.left, b.w⟩ a.left hb'
  apply Over.OverMorphism.ext
  exact h

#print axioms solution
