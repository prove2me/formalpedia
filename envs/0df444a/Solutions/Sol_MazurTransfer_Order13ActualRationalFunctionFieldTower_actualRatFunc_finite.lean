-- Prove2me | solution 1 for MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFunc_finite
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T08:15:40.964395+00:00
-- url     : https://prove2.me/submissions/04c4a568-8ef2-4359-b458-3cbd7224e9d6

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual order-13 function field is finite over the
rational function field via its existing transcendental x-coordinate.
Named downstream consumer: instantiate the divisibility-based injectivity
result for the actual divisorial nineteen-pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
noncomputable section
open MazurTransfer
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13FieldHyperellipticFixedField Order13ActualRationalFunctionFieldTower
attribute [local instance] actualRatFuncTowerOriginalFactProvider20261018 actualRatFuncTowerOriginalAlgebraProvider20261018
variable (K : Type*) [Field K] [CharZero K]
local instance finiteTowerOriginalRatFuncAlgebraProvider20261018 : Algebra (RatFunc K) (actualCurveFunctionField K) := actualRatFuncAlgebra K

theorem solution : FiniteDimensional (RatFunc K) (actualCurveFunctionField K) := by
  let ε := rationalInvolutionFieldEquiv K
  letI : Algebra (RatFunc K) (xField K) := ε.toAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower (RatFunc K) (xField K) (actualCurveFunctionField K) :=
    IsScalarTower.of_algebraMap_eq fun z => rfl
  letI : FiniteDimensional (xField K) (actualCurveFunctionField K) := curveField_finite K
  letI : Module.Finite (RatFunc K) (xField K) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) (xField K)) ε.surjective
  exact Module.Finite.trans (xField K) (actualCurveFunctionField K)

#print axioms solution
