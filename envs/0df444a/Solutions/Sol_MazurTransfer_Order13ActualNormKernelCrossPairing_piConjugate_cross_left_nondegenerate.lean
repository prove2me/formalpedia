-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCrossPairing.piConjugate_cross_left_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T12:56:24.895542+00:00
-- url     : https://prove2.me/submissions/60bda86d-67f3-4eda-a860-8ae106b24658

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: nondegeneracy of the actual divisorial nineteen pairing
between the actual pi and conjugate-pi restricted kernels.
Named downstream consumer: actual norm-kernel cyclotomic character quotients. -/
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
import Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDiamondComparison_geometricNineteenTorsionDivisorAddEquiv_diamond
import Theorems.Thm_MazurTransfer_Order13ActualDivisorialPairingPerfect_actualPairing_perfect
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_finite
import Theorems.Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint
noncomputable section
namespace MazurTransfer.ActualConjugateNormKernelCrossPairingProofHelpers20261018
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardGeometricNormPreimages
open Order13ActualNormKernelProductCardinality
open Order13ActualPicardAlgPointsComparison
open Order13ActualPicardGeometricArithmeticGroup
open Order13ActualPicardGeometricDiamondGroupAction
open scoped CategoryTheory.MonObj
open Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualGeometricNineteenTorsionDiamondComparison
open Order13ActualNineteenTorsionPairingTransport
open Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualNormKernelRanksFromPerfectDivisorialPairing
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardNormKummerCocycles
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018
attribute [local instance] pairingTransportOriginalFactProvider20261018
  pairingTransportOriginalAlgebraProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
variable (d : DivisorialWeilPairingData K (actualCurveFunctionField K) 19)

theorem pairingUnits_add_left (x x' y : NineteenTorsion K) :
    pairingUnits K d (x + x') y = pairingUnits K d x y * pairingUnits K d x' y := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K (x + x'))
    (geometricNineteenTorsionDivisorAddEquiv K y) = _
  rw [map_add]
  exact d.pair_add_left _ _ _

theorem pairingUnits_add_right (x y y' : NineteenTorsion K) :
    pairingUnits K d x (y + y') = pairingUnits K d x y * pairingUnits K d x y' := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K x)
    (geometricNineteenTorsionDivisorAddEquiv K (y + y')) = _
  rw [map_add]
  exact d.pair_add_right _ _ _

theorem pairingUnits_mul_swap (x y : NineteenTorsion K) :
    pairingUnits K d x y * pairingUnits K d y x = 1 := by
  apply Units.ext
  exact d.pair_mul_pair_swap _ _

theorem pairingUnits_diamond (x y : NineteenTorsion K) :
    pairingUnits K d (actualNineteenTorsionDiamondHom K x) (actualNineteenTorsionDiamondHom K y) =
      pairingUnits K d x y := by
  apply Units.ext
  change d.pair
    (geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionDiamondHom K x))
    (geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionDiamondHom K y)) = _
  rw [geometricNineteenTorsionDivisorAddEquiv_diamond,
    geometricNineteenTorsionDivisorAddEquiv_diamond]
  exact d.pair_smul (Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv K) _ _

theorem pairingUnits_left_nondegenerate (hd : d.Perfect) (x : NineteenTorsion K)
    (hx : ∀ y, pairingUnits K d x y = 1) : x = 0 := by
  apply (geometricNineteenTorsionDivisorAddEquiv K).injective
  rw [map_zero]
  apply (d.toWeilPairingData hd).eq_zero_of_forall_eval_eq_one
  intro y
  obtain ⟨z, rfl⟩ := (geometricNineteenTorsionDivisorAddEquiv K).surjective y
  exact congrArg Units.val (hx z)

theorem pairingUnits_right_nondegenerate (hd : d.Perfect) (y : NineteenTorsion K)
    (hy : ∀ x, pairingUnits K d x y = 1) : y = 0 := by
  apply pairingUnits_left_nondegenerate K d hd y
  intro x
  have h := pairingUnits_mul_swap K d x y
  rw [hy x, one_mul] at h
  exact h

theorem diamond_square_apply (x : NineteenTorsion K) :
    actualNineteenTorsionDiamondHom K (actualNineteenTorsionDiamondHom K x) =
      actualNineteenTorsionDiamondHom K x - x := by
  apply (geometricNineteenTorsionDivisorAddEquiv K).injective
  rw [geometricNineteenTorsionDivisorAddEquiv_diamond,
    geometricNineteenTorsionDivisorAddEquiv_diamond, map_sub,
    geometricNineteenTorsionDivisorAddEquiv_diamond]
  apply Subtype.ext
  change ((Order13FieldDiamondPicardEndomorphisms.rho K) ^ 2)
    (geometricNineteenTorsionDivisorAddEquiv K x).val = _
  exact Order13FieldPicardCyclotomicNorm.rho_square_apply K _

theorem diamond_sub_inverse (y : NineteenTorsion K) :
    actualNineteenTorsionDiamondHom K (y - actualNineteenTorsionDiamondHom K y) = y := by
  rw [map_sub, diamond_square_apply]
  abel



theorem pairingUnits_diamond_adjoint (x y : NineteenTorsion K) :
    pairingUnits K d (actualNineteenTorsionDiamondHom K x) y =
      pairingUnits K d x (y - actualNineteenTorsionDiamondHom K y) := by
  have h := pairingUnits_diamond K d x (y - actualNineteenTorsionDiamondHom K y)
  rw [diamond_sub_inverse] at h
  exact h

theorem pairingUnits_zero_left (y : NineteenTorsion K) : pairingUnits K d 0 y = 1 := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K 0)
    (geometricNineteenTorsionDivisorAddEquiv K y) = 1
  rw [map_zero]
  exact d.pair_zero_left _

theorem pairingUnits_zero_right (x : NineteenTorsion K) : pairingUnits K d x 0 = 1 := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K x)
    (geometricNineteenTorsionDivisorAddEquiv K 0) = 1
  rw [map_zero]
  exact d.pair_zero_right _

theorem pairingUnits_nsmul_left (n : ℕ) (x y : NineteenTorsion K) :
    pairingUnits K d (n • x) y = pairingUnits K d x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pairingUnits_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, pairingUnits_add_left, ih, pow_succ]

theorem pairingUnits_nsmul_right (n : ℕ) (x y : NineteenTorsion K) :
    pairingUnits K d x (n • y) = pairingUnits K d x y ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pairingUnits_zero_right, pow_zero]
  | succ n ih => rw [succ_nsmul, pairingUnits_add_right, ih, pow_succ]

theorem normPi_apply (x : NineteenTorsion K) :
    actualNineteenTorsionNormHom K schemePi x =
      (3 : ℕ) • x + (2 : ℕ) • actualNineteenTorsionDiamondHom K x := by
  apply Subtype.ext
  change (x.val.toMul ≫ schemePi) = x.val.toMul ^ 3 * (x.val.toMul ≫ schemeDiamond) ^ 2
  simp only [schemePi, MonObj.comp_mul, MonObj.comp_pow, Category.comp_id]

theorem normPiConjugate_apply (x : NineteenTorsion K) :
    actualNineteenTorsionNormHom K schemePiConjugate x =
      (5 : ℕ) • x - (2 : ℕ) • actualNineteenTorsionDiamondHom K x := by
  apply Subtype.ext
  change (x.val.toMul ≫ schemePiConjugate) =
    x.val.toMul ^ 5 * ((x.val.toMul ≫ schemeDiamond) ^ 2)⁻¹
  simp only [schemePiConjugate, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, Category.comp_id]

theorem pairingUnits_norm_adjoint (x y : NineteenTorsion K) :
    pairingUnits K d (actualNineteenTorsionNormHom K schemePi x) y =
      pairingUnits K d x (actualNineteenTorsionNormHom K schemePiConjugate y) := by
  rw [normPi_apply, pairingUnits_add_left, pairingUnits_nsmul_left,
    pairingUnits_nsmul_left, pairingUnits_diamond_adjoint,
    ← pairingUnits_nsmul_right, ← pairingUnits_nsmul_right, ← pairingUnits_add_right]
  congr 1
  rw [normPiConjugate_apply]
  abel


open Order13ActualGeometricNineteenDivisorialPairing Order13ActualDivisorialPairingPerfect
theorem actualPairing_add_right (x y y' : NineteenTorsion K) :
    actualGeometricNineteenPairing K x (y + y') =
      actualGeometricNineteenPairing K x y * actualGeometricNineteenPairing K x y' :=
  pairingUnits_add_right K _ x y y'


theorem actualPairing_mul_swap (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K x y * actualGeometricNineteenPairing K y x = 1 :=
  pairingUnits_mul_swap K _ x y


theorem actualPairing_pow_nineteen (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K x y ^ 19 = 1 := by
  have hx : (19 : ℕ) • x = 0 := by
    apply Subtype.ext
    exact x.property
  change pairingUnits K (actualDivisorialNineteenPairingData K) x y ^ 19 = 1
  rw [← pairingUnits_nsmul_left, hx, pairingUnits_zero_left]


theorem actualPairing_norm_adjoint (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K (actualNineteenTorsionNormHom K schemePi x) y =
      actualGeometricNineteenPairing K x (actualNineteenTorsionNormHom K schemePiConjugate y) :=
  pairingUnits_norm_adjoint K _ x y


theorem actualPairing_left_nondegenerate (x : NineteenTorsion K)
    (hx : ∀ y, actualGeometricNineteenPairing K x y = 1) : x = 0 :=
  pairingUnits_left_nondegenerate K _ (actualPairing_perfect K) x hx


theorem pow_eight_nineteen_eq_one (u : Kˣ) (h8 : u ^ 8 = 1) (h19 : u ^ 19 = 1) : u = 1 := by
  have h96 : u ^ 96 = 1 := by
    rw [show (96 : ℕ) = 8 * 12 from rfl, pow_mul, h8, one_pow]
  have h95 : u ^ 95 = 1 := by
    rw [show (95 : ℕ) = 19 * 5 from rfl, pow_mul, h19, one_pow]
  have h : u ^ 96 = u := by
    rw [show (96 : ℕ) = 95 + 1 from rfl, pow_succ, h95, one_mul]
  exact h.symm.trans h96


theorem norm_sum (x : NineteenTorsion K) :
    actualNineteenTorsionNormHom K schemePi x +
      actualNineteenTorsionNormHom K schemePiConjugate x = (8 : ℕ) • x := by
  rw [normPi_apply, normPiConjugate_apply]
  abel


theorem normPi_normPiConjugate (x : NineteenTorsion K) :
    actualNineteenTorsionNormHom K schemePi
      (actualNineteenTorsionNormHom K schemePiConjugate x) = 0 := by
  apply Subtype.ext
  change (x.val.toMul ≫ schemePiConjugate) ≫ schemePi = 1
  rw [Category.assoc, schemePiConjugate_comp_schemePi, MonObj.comp_pow, Category.comp_id]
  have hx : (19 : ℕ) • x.val = 0 := x.property
  exact hx


theorem normPiConjugate_normPi (x : NineteenTorsion K) :
    actualNineteenTorsionNormHom K schemePiConjugate
      (actualNineteenTorsionNormHom K schemePi x) = 0 := by
  apply Subtype.ext
  change (x.val.toMul ≫ schemePi) ≫ schemePiConjugate = 1
  rw [Category.assoc, schemePi_comp_schemePiConjugate, MonObj.comp_pow, Category.comp_id]
  have hx : (19 : ℕ) • x.val = 0 := x.property
  exact hx


theorem actualPairing_nsmul_right (n : ℕ) (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K x (n • y) = actualGeometricNineteenPairing K x y ^ n :=
  pairingUnits_nsmul_right K (actualDivisorialNineteenPairingData K) n x y


theorem actualPairing_zero_left (y : NineteenTorsion K) : actualGeometricNineteenPairing K 0 y = 1 :=
  pairingUnits_zero_left K (actualDivisorialNineteenPairingData K) y


end MazurTransfer.ActualConjugateNormKernelCrossPairingProofHelpers20261018
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelProductCardinality
open Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualNormKernelRanksFromPerfectDivisorialPairing
open Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualDivisorialPairingPerfect
open Order13ActualNineteenTorsionPairingTransport
open ActualConjugateNormKernelCrossPairingProofHelpers20261018
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018
attribute [local instance] pairingTransportOriginalFactProvider20261018
  pairingTransportOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (x : (actualNineteenTorsionNormHom K schemePiConjugate).ker)
    (h : ∀ y : (actualNineteenTorsionNormHom K schemePi).ker,
      actualGeometricNineteenPairing K x.val y.val = 1) : x = 0 := by
  apply Subtype.ext
  apply actualPairing_left_nondegenerate K x.val
  intro y
  apply pow_eight_nineteen_eq_one K _ _ (actualPairing_pow_nineteen K _ _)
  rw [← actualPairing_nsmul_right, ← norm_sum, actualPairing_add_right]
  have hbar := h ⟨actualNineteenTorsionNormHom K schemePiConjugate y, normPi_normPiConjugate K y⟩
  rw [hbar, mul_one]
  have ha := actualPairing_norm_adjoint K y x.val
  rw [x.property] at ha
  have hz : actualGeometricNineteenPairing K y 0 = 1 :=
    pairingUnits_zero_right K (actualDivisorialNineteenPairingData K) y
  rw [hz] at ha
  have hs := actualPairing_mul_swap K x.val (actualNineteenTorsionNormHom K schemePi y)
  rw [ha, mul_one] at hs
  exact hs

#print axioms solution
