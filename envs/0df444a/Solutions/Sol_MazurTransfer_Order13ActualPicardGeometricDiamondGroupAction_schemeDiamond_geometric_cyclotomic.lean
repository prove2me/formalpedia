-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction.schemeDiamond_geometric_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:44:50.245518+00:00
-- url     : https://prove2.me/submissions/a78baea5-fe78-4e97-9e6b-67ce905aefaa

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual rational Picard diamond satisfies its
cyclotomic and hyperelliptic identities on every perfect characteristic-zero
field point, via the injective geometric divisor-class group map.
Named downstream consumer: the same identities as equalities of actual
Picard scheme morphisms, and the nineteen-norm endomorphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017
import Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_actualGenericDiamondHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective_explicitOriginalType20261017

noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open scoped CategoryTheory.MonObj
local instance geometricDiamondCyclotomicPointProvider120261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance geometricDiamondCyclotomicPointProvider220261017 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance geometricDiamondCyclotomicPointProvider320261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.GeometricDiamondGroupActionUnitHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance geometricDiamondCyclotomicPointProvider420261017 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance geometricDiamondCyclotomicPointProvider520261017 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)


namespace MazurTransfer.GeometricDiamondCyclotomicPointHelpers20261017
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


end MazurTransfer.GeometricDiamondCyclotomicPointHelpers20261017
open MazurTransfer.GeometricDiamondCyclotomicPointHelpers20261017
include 𝒱 in
theorem solution
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    ((a ≫ schemeDiamond ≫ schemeDiamond) * (a ≫ schemeDiamond)⁻¹) * a = 1 := by
  apply geometricArithmeticClassOver_injective_explicitOriginalType20261017 K 𝒱
  rw [geometricArithmeticClassOver_mul, geometricArithmeticClassOver_mul,
    geometricArithmeticClassOver_inv, geometricArithmeticClassOver_one,
    geometricArithmeticClassOver_schemeDiamond_square, geometricArithmeticClassOver_schemeDiamond,
    Order13FieldPicardCyclotomicNorm.rho_square_apply]
  abel


#print axioms solution
