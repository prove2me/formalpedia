-- Prove2me | solution 1 for MazurTransfer.Order13ActualDivisorialPairingPerfect.actualPairing_perfect
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T11:33:58.949911+00:00
-- url     : https://prove2.me/submissions/45a046dd-0f12-434c-b940-d97e56921e6d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: perfection of the SAME original actual divisorial
nineteen-pairing, using proved character-map injectivity and finite
arithmetic torsion obtained from the natural actual Picard equivalence.
Named downstream consumer: individual actual norm-kernel ranks from
pairing adjointness. No perfection or injectivity hypothesis is supplied.
-/
import Definitions.Def_MazurTransfer_Order13ActualDivisorialNineteenPairingOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNaturalNineteenTorsionDivisorAddEquivData20261018
import Theorems.Thm_MazurTransfer_Order13ActualDivisorialPairingPerfect_actualPairing_toHom_injective
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_finite
import Theorems.Thm_MazurTransfer_FiniteDivisorialPairingPerfectOfInjective_perfect_of_toHom_injective
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualGeometricNineteenDivisorialPairing Order13ActualDivisorialPairingPerfect
attribute [local instance] actualDivisorialPairingOriginalFactProvider20261018 actualDivisorialPairingOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    (actualDivisorialNineteenPairingData K).Perfect := by
  letI : Finite (NineteenTorsion K) := nineteenTorsion_finite K
  letI : Finite (Pic0.torsion K (actualCurveFunctionField K) 19) :=
    Finite.of_equiv (NineteenTorsion K) (geometricNineteenTorsionDivisorAddEquiv K).toEquiv
  exact FiniteDivisorialPairingPerfectOfInjective.perfect_of_toHom_injective _
    (actualPairing_toHom_injective K)

#print axioms solution
