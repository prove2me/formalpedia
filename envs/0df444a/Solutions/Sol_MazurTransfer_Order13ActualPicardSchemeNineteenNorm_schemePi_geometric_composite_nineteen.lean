-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePi_geometric_composite_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:42:45.786999+00:00
-- url     : https://prove2.me/submissions/f308daed-8b40-49f2-add3-ed80b3c7e60c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two explicit endomorphisms of the same rational Picard
scheme have both composites equal to scalar nineteen. This establishes
the actual scheme norm identity; isogeny properties and degrees remain
separate obligations. Named downstream consumer: nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_actualGenericDiamondHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective_explicitOriginalType20261017

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance schemeNineteenNormForwardPointProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance schemeNineteenNormForwardPointProvider220261017 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance schemeNineteenNormForwardPointProvider320261017 : Algebra K (GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionField K) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra K
variable (𝒱 : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover)


namespace MazurTransfer.SchemeNineteenNormForwardPointHelpers20261017
theorem geometricArithmeticClassOver_inv
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    geometricArithmeticClassOver K 𝒱 a⁻¹ = -geometricArithmeticClassOver K 𝒱 a := by
  exact congrArg Multiplicative.toAdd (map_inv (geometricClassHom K 𝒱) a)

theorem geometricArithmeticClassOver_schemeDiamond
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    geometricArithmeticClassOver K 𝒱 (a ≫ schemeDiamond) =
      (Order13FieldDiamondPicardEndomorphisms.rho K) (geometricArithmeticClassOver K 𝒱 a) := by
  exact geometricArithmeticClass_actualGenericDiamondHom K 𝒱 (pointOfOverHom K a)

theorem geometricArithmeticClassOver_schemeDiamond_square
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    geometricArithmeticClassOver K 𝒱 (a ≫ schemeDiamond ≫ schemeDiamond) =
      (Order13FieldDiamondPicardEndomorphisms.rho K ^ 2) (geometricArithmeticClassOver K 𝒱 a) := by
  rw [← Category.assoc, geometricArithmeticClassOver_schemeDiamond,
    geometricArithmeticClassOver_schemeDiamond]
  rfl


theorem geometricArithmeticClassOver_pow
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase)
    (n : ℕ) : geometricArithmeticClassOver K 𝒱 (a ^ n) = n • geometricArithmeticClassOver K 𝒱 a :=
  congrArg Multiplicative.toAdd (map_pow (geometricClassHom K 𝒱) a n)

theorem geometricArithmeticClassOver_schemePi
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    geometricArithmeticClassOver K 𝒱 (a ≫ schemePi) =
      (Order13FieldDiamondPicardEndomorphisms.pi K) (geometricArithmeticClassOver K 𝒱 a) := by
  rw [schemePi, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
    geometricArithmeticClassOver_mul, geometricArithmeticClassOver_pow,
    geometricArithmeticClassOver_pow, geometricArithmeticClassOver_schemeDiamond]
  rfl

theorem geometricArithmeticClassOver_schemePiConjugate
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    geometricArithmeticClassOver K 𝒱 (a ≫ schemePiConjugate) =
      (Order13FieldDiamondPicardEndomorphisms.piConjugate K) (geometricArithmeticClassOver K 𝒱 a) := by
  rw [schemePiConjugate, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv,
    MonObj.comp_pow, Category.comp_id, geometricArithmeticClassOver_mul,
    geometricArithmeticClassOver_inv, geometricArithmeticClassOver_pow,
    geometricArithmeticClassOver_pow, geometricArithmeticClassOver_schemeDiamond]
  change (5 : ℕ) • geometricArithmeticClassOver K 𝒱 a +
    -((2 : ℕ) • (Order13FieldDiamondPicardEndomorphisms.rho K) (geometricArithmeticClassOver K 𝒱 a)) =
    (5 : ℕ) • geometricArithmeticClassOver K 𝒱 a -
    (2 : ℕ) • (Order13FieldDiamondPicardEndomorphisms.rho K) (geometricArithmeticClassOver K 𝒱 a)
  exact (sub_eq_add_neg _ _).symm


end MazurTransfer.SchemeNineteenNormForwardPointHelpers20261017
open MazurTransfer.SchemeNineteenNormForwardPointHelpers20261017
include 𝒱 in
theorem solution
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    a ≫ schemePi ≫ schemePiConjugate = a ^ 19 := by
  apply geometricArithmeticClassOver_injective_explicitOriginalType20261017 K 𝒱
  rw [← Category.assoc, geometricArithmeticClassOver_schemePiConjugate,
    geometricArithmeticClassOver_schemePi, geometricArithmeticClassOver_pow]
  exact congrArg (fun f : AddMonoid.End (Order13FieldDiamondPicardEndomorphisms.ActualPicard K) =>
    f (geometricArithmeticClassOver K 𝒱 a))
    (Order13FieldPicardCyclotomicNorm.piConjugate_comp_pi_nineteen K)


#print axioms solution
