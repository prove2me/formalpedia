-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelRanksTwo.actual_norm_kernel_cards_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T12:22:42.363018+00:00
-- url     : https://prove2.me/submissions/16ab4a91-30e8-4987-85e5-b5c4ca476e2e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses finite character counting from official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: equality of the two complete actual Picard norm-kernel
cardinalities from the constructed perfect actual divisorial pairing.
Named downstream consumer: individual actual norm-kernel dimensions two.
-/
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
import Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDiamondComparison_geometricNineteenTorsionDivisorAddEquiv_diamond
import Theorems.Thm_MazurTransfer_Order13ActualDivisorialPairingPerfect_actualPairing_perfect
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_finite
import Theorems.Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint
noncomputable section
namespace MazurTransfer.FiniteNondegenerateAdjointKernelProofHelpers20261018
open scoped Classical
scoped instance finite_monoidHom_units (G : Type*) [CommGroup G] [Finite G] (K : Type*) [Field K] : Finite (G →* Kˣ) := by
  classical
  haveI := Fintype.ofFinite G
  have hexp : 0 < Monoid.exponent G := Monoid.exponent_pos.mpr Monoid.ExponentExists.of_finite
  let n : ℕ+ := ⟨Monoid.exponent G, hexp⟩
  let F : (G →* Kˣ) → (G → rootsOfUnity n K) := fun χ g =>
    ⟨χ g, by
      rw [mem_rootsOfUnity]
      show (χ g) ^ Monoid.exponent G = 1
      rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]⟩
  refine Finite.of_injective F fun χ χ' h => ?_
  ext g
  have := congrArg (fun f => ((f g : rootsOfUnity n K) : Kˣ)) h
  exact congrArg Units.val this

theorem natCard_monoidHom_units_le (G : Type*) [CommGroup G] [Finite G] (K : Type*) [Field K] :
    Nat.card (G →* Kˣ) ≤ Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite (G →* Kˣ)

  let ι : (G →* Kˣ) → (G →* K) := fun χ => (Units.coeHom K).comp χ
  have hι : Function.Injective ι := by
    intro χ χ' h; ext g
    have := DFunLike.congr_fun h g
    exact this
  have hli : LinearIndependent K (fun χ : G →* Kˣ => ((ι χ : G →* K) : G → K)) :=
    (linearIndependent_monoidHom G K).comp ι hι
  have h1 := hli.fintype_card_le_finrank
  rw [Module.finrank_pi K, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h1
  exact h1



variable {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]

theorem character_surjective_of_nondegenerate
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
    (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hright : ∀ y, (∀ x, e x y = 1) → y = 0) :
    ∀ χ : Multiplicative P →* Kˣ, ∃ y, ∀ x, e x y = χ (Multiplicative.ofAdd x) := by
  letI : Finite (Multiplicative P →* Kˣ) := finite_monoidHom_units _ K
  let cr : P → (Multiplicative P →* Kˣ) := fun y =>
    { toFun := fun x => e x.toAdd y
      map_one' := by
        change e 0 y = 1
        have h := hadd₁ 0 0 y
        rw [zero_add] at h
        exact mul_eq_left.mp h.symm
      map_mul' := fun x x' => hadd₁ x.toAdd x'.toAdd y }
  have hi : Function.Injective cr := by
    intro y y' h
    have hz : ∀ x, e x (y - y') = 1 := by
      intro x
      have hh : e x y = e x y' := DFunLike.congr_fun h (Multiplicative.ofAdd x)
      have ha := hadd₂ x (y - y') y'
      rw [sub_add_cancel, hh] at ha
      exact mul_eq_right.mp ha.symm
    exact sub_eq_zero.mp (hright _ hz)
  have hc : Nat.card (Multiplicative P →* Kˣ) ≤ Nat.card P := by
    have hc := natCard_monoidHom_units_le (Multiplicative P) K
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative P ≃ P)] at hc
    exact hc
  have hs := (hi.bijective_of_nat_card_le hc).2
  intro χ
  obtain ⟨y, hy⟩ := hs χ
  exact ⟨y, fun x => DFunLike.congr_fun hy (Multiplicative.ofAdd x)⟩

end MazurTransfer.FiniteNondegenerateAdjointKernelProofHelpers20261018

namespace MazurTransfer.ActualNormKernelCardinalityProofHelpers20261018
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

end MazurTransfer.ActualNormKernelCardinalityProofHelpers20261018
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
open ActualNormKernelCardinalityProofHelpers20261018
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018
attribute [local instance] pairingTransportOriginalFactProvider20261018
  pairingTransportOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Nat.card (Kernel K schemePi) = Nat.card (Kernel K schemePiConjugate) := by
  let d := actualDivisorialNineteenPairingData K
  have hd : d.Perfect := actualPairing_perfect K
  letI : Finite (NineteenTorsion K) := nineteenTorsion_finite K
  have hrestricted : Nat.card (actualNineteenTorsionNormHom K schemePi).ker =
      Nat.card (actualNineteenTorsionNormHom K schemePiConjugate).ker :=
    AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint
      (pairingUnits K d) (pairingUnits_add_left K d) (pairingUnits_add_right K d)
      (pairingUnits_left_nondegenerate K d hd) (pairingUnits_right_nondegenerate K d hd)
      (FiniteNondegenerateAdjointKernelProofHelpers20261018.character_surjective_of_nondegenerate
        (pairingUnits K d) (pairingUnits_add_left K d) (pairingUnits_add_right K d)
        (pairingUnits_right_nondegenerate K d hd))
      (actualNineteenTorsionNormHom K schemePi) (actualNineteenTorsionNormHom K schemePiConjugate)
      (pairingUnits_norm_adjoint K d)
  exact (Nat.card_congr (restrictedPiKernelEquiv K)).symm.trans
    (hrestricted.trans (Nat.card_congr (restrictedPiConjugateKernelEquiv K)))

#print axioms solution
