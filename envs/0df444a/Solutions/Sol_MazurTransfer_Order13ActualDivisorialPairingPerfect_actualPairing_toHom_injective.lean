-- Prove2me | solution 1 for MazurTransfer.Order13ActualDivisorialPairingPerfect.actualPairing_toHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T11:23:43.536449+00:00
-- url     : https://prove2.me/submissions/dd68200e-df0b-43e8-8a0f-0b24e25376f5

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the exact accepted Picard-divisibility contract and official Anthropic
FLT divisorial character-map injectivity, Apache-2.0, exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: character-map injectivity for the original actual
divisorial nineteen-pairing, deriving divisibility from the rational
function-field tower rather than supplying it as a hypothesis.
Named downstream consumer: perfection of the same actual pairing and
unconditional ranks of the two actual Picard norm kernels.
-/
import Definitions.Def_MazurTransfer_Order13ActualDivisorialNineteenPairingOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
import Theorems.Thm_MazurTransfer_Order13ActualRationalFunctionFieldTower_actualRatFunc_finite
import Theorems.Thm_MazurTransfer_FiniteRatFuncPicardDivisible_picard_divisible_of_finite_ratFunc
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualRationalFunctionFieldTower Order13ActualGeometricNineteenDivisorialPairing
attribute [local instance] actualDivisorialPairingOriginalFactProvider20261018 actualDivisorialPairingOriginalAlgebraProvider20261018 actualRatFuncAlgebra

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Function.Injective (actualDivisorialNineteenPairingData K).toHom := by
  letI : IsScalarTower K (RatFunc K) (actualCurveFunctionField K) :=
    IsScalarTower.of_algebraMap_eq fun c => ((actualRatFuncEmbedding K).commutes c).symm
  letI : FiniteDimensional (RatFunc K) (actualCurveFunctionField K) := actualRatFunc_finite K
  apply DivisorialWeilPairingData.toHom_injective_of_divisible ?_ (actualDivisorialNineteenPairingData K)
  intro L' _ _ _ _ _ m hm x
  exact FiniteRatFuncPicardDivisible.picard_divisible_of_finite_ratFunc (K := K) L' m hm x

#print axioms solution
