-- Prove2me | solution 1 for MazurTransfer.order13_actual_pairing_self_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T22:19:58.599311+00:00
-- url     : https://prove2.me/submissions/c1332a0c-51c5-4e38-b728-b54addf289d3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: reflection exchanges the actual restricted norm kernels,
preserves the SAME actual nineteen-pairing, and pairs trivially with its own
input. Named downstream consumer: identifying the one-dimensional kernel
of the actual cyclotomic quotient by its reflection-generated line.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Theorems.Thm_MazurTransfer_Order13ActualNineteenTorsionReflection_pairingUnits_reflection
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualGeometricNineteenTorsionDivisorComparison Order13ActualNineteenTorsionPairingTransport
open Order13ReflectionParameter Order13FieldPicardReflection Order13ActualNineteenTorsionReflection
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalGroupProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalCommProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalDiamondHomProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalFactProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalAlgebraProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalPiHomProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalConjugateHomProvider20261018
open Order13ActualGeometricNineteenDivisorialPairing
namespace MazurTransfer.ActualPairingSelfReflectionMinimalDependenciesProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
section PairingLaws
variable (d : DivisorialWeilPairingData K (actualCurveFunctionField K) 19)
theorem pairingUnits_add_left (x x' y : NineteenTorsion K) :
    pairingUnits K d (x + x') y = pairingUnits K d x y * pairingUnits K d x' y := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K (x + x'))
    (geometricNineteenTorsionDivisorAddEquiv K y) = _
  rw [map_add]
  exact d.pair_add_left _ _ _

theorem pairingUnits_zero_left (y : NineteenTorsion K) : pairingUnits K d 0 y = 1 := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K 0)
    (geometricNineteenTorsionDivisorAddEquiv K y) = 1
  rw [map_zero]
  exact d.pair_zero_left _

theorem pairingUnits_nsmul_left (n : ℕ) (x y : NineteenTorsion K) :
    pairingUnits K d (n • x) y = pairingUnits K d x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pairingUnits_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, pairingUnits_add_left, ih, pow_succ]

end PairingLaws
theorem actualPairing_pow_nineteen (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K x y ^ 19 = 1 := by
  have hx : (19 : ℕ) • x = 0 := by
    apply Subtype.ext
    exact x.property
  change pairingUnits K (actualDivisorialNineteenPairingData K) x y ^ 19 = 1
  rw [← pairingUnits_nsmul_left, hx, pairingUnits_zero_left]

theorem actualReflection_involution (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K a (actualReflection K a x) = x := by
  exact (actualReflection K a).left_inv x
theorem pow_eight_nineteen_eq_one (u : Kˣ) (h8 : u ^ 8 = 1) (h19 : u ^ 19 = 1) : u = 1 := by
  have h96 : u ^ 96 = 1 := by
    rw [show (96 : ℕ) = 8 * 12 from rfl, pow_mul, h8, one_pow]
  have h95 : u ^ 95 = 1 := by
    rw [show (95 : ℕ) = 19 * 5 from rfl, pow_mul, h19, one_pow]
  have h : u ^ 96 = u := by
    rw [show (96 : ℕ) = 95 + 1 from rfl, pow_succ, h95, one_mul]
  exact h.symm.trans h96

theorem actualPairing_mul_swap (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K x y * actualGeometricNineteenPairing K y x = 1 := by
  apply Units.ext
  exact (actualDivisorialNineteenPairingData K).pair_mul_pair_swap _ _
theorem actualPairing_reflection (a : ReflectionParameter K) (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K (actualReflection K a x) (actualReflection K a y) =
      actualGeometricNineteenPairing K x y :=
  pairingUnits_reflection K a (actualDivisorialNineteenPairingData K) x y

end MazurTransfer.ActualPairingSelfReflectionMinimalDependenciesProofHelpers20261018
open MazurTransfer.ActualPairingSelfReflectionMinimalDependenciesProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem solution (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualGeometricNineteenPairing K x (actualReflection K a x) = 1 := by
  have h := actualPairing_reflection K a x (actualReflection K a x)
  rw [actualReflection_involution K a] at h
  have hs := actualPairing_mul_swap K x (actualReflection K a x)
  rw [h] at hs
  have h2 : actualGeometricNineteenPairing K x (actualReflection K a x) ^ 2 = 1 := by
    simpa only [pow_two] using hs
  apply pow_eight_nineteen_eq_one K _ _ (actualPairing_pow_nineteen K x (actualReflection K a x))
  calc
    _ = (actualGeometricNineteenPairing K x (actualReflection K a x) ^ 2) ^ 4 := by group
    _ = 1 := by rw [h2, one_pow]


#print axioms solution
