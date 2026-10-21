-- Prove2me | solution 1 for MazurTransfer.original_integral_hopf_arithmetic_kernel_labels_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T04:28:29.233857+00:00
-- url     : https://prove2.me/submissions/821f759a-326d-4fa5-a291-93d85df9fc94

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: label the same integral Hopf points by the previously fixed arithmetic norm kernel and existing additive Galois action, preserving multiplication and spectrum precomposition.
Named downstream consumer: actual finite-flat ordered character quotients.
-/
import Definitions.Def_MazurTransfer_OriginalIntegralHopfArithmeticKernelLabelsData20261020
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_norm_kernel_comparison_laws
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralArithmeticNormKernelComparison MazurTransfer.Order13IntegralArithmeticFieldPointComparison
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardGeometricNormPreimages MazurTransfer.Order13ActualPicardNormKummerCocycles
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13IntegralHopfArithmeticKernelLabels
attribute [local instance] MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralHopfArithmeticKernelLabels
attribute [local instance] MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels
attribute [local instance] MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels
namespace MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsBoundary20261020
end MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: label the SAME integral Hopf points by the PREVIOUSLY
FIXED arithmetic norm kernel and its existing additive Galois action.
The point equivalence must preserve multiplication and spectrum
precomposition, not merely cardinality or abstract module isomorphism.
Named downstream consumer: actual finite-flat ordered character quotients.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralArithmeticNormKernelComparison Order13IntegralArithmeticFieldPointComparison
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ActualArithmeticKernelAdditiveAction
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]

variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]


variable {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H]
variable (e : WithConv (H →ₐ[LocalRing q] K) ≃
  kernelPoints (localLaw q hq) (integralNorm q hq φ)
    (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K))



theorem fixedKernelLabel_mul
    (hMul : ∀ f g, (e (f * g)).val = (localLaw q hq).mul _ (e f).val (e g).val)
    (f g : WithConv (H →ₐ[LocalRing q] K)) :
    fixedKernelLabel q hq K φ e (f * g) =
      fixedKernelLabel q hq K φ e f * fixedKernelLabel q hq K φ e g := by
  apply (kernelPointEquiv q hq K φ).injective
  apply Subtype.ext
  change ((kernelPointEquiv q hq K φ) ((kernelPointEquiv q hq K φ).symm (e (f * g)))).val =
    ((kernelPointEquiv q hq K φ)
      ((kernelPointEquiv q hq K φ).symm (e f) * (kernelPointEquiv q hq K φ).symm (e g))).val
  rw [(MazurTransfer.original_integral_arithmetic_norm_kernel_comparison_laws).1]
  simp only [Equiv.apply_symm_apply]
  exact hMul f g

theorem fixedKernelLabel_act (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (H →ₐ[LocalRing q] K))
    (hNat : (e g).val.val = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e f).val.val) :
    fixedKernelLabel q hq K φ e g = σ • fixedKernelLabel q hq K φ e f := by
  apply (kernelPointEquiv q hq K φ).injective
  apply Subtype.ext
  apply Subtype.ext
  change ((kernelPointEquiv q hq K φ) ((kernelPointEquiv q hq K φ).symm (e g))).val.val =
    ((kernelPointEquiv q hq K φ) (σ • (kernelPointEquiv q hq K φ).symm (e f))).val.val
  rw [(MazurTransfer.original_integral_arithmetic_norm_kernel_comparison_laws).2]
  simpa only [Equiv.apply_symm_apply, GoodReductionJacobian.schemeHomOverComp] using hNat



theorem arithmeticKernelLabel_add
    (hMul : ∀ f g, (e (f * g)).val = (localLaw q hq).mul _ (e f).val (e g).val)
    (f g : WithConv (H →ₐ[LocalRing q] K)) :
    arithmeticKernelLabel q hq K φ e (f * g) =
      arithmeticKernelLabel q hq K φ e f + arithmeticKernelLabel q hq K φ e g :=
  congrArg Additive.ofMul (fixedKernelLabel_mul q hq K φ e hMul f g)

theorem arithmeticKernelLabel_act (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (H →ₐ[LocalRing q] K))
    (hNat : (e g).val.val = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e f).val.val) :
    arithmeticKernelLabel q hq K φ e g = σ • arithmeticKernelLabel q hq K φ e f :=
  congrArg Additive.ofMul (fixedKernelLabel_act q hq K φ e σ f g hNat)

end MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (hMul : ∀ f g, (e (f * g)).val = (localLaw q hq).mul _ (e f).val (e g).val)
    (f g : WithConv (H →ₐ[LocalRing q] K)),
fixedKernelLabel q hq K φ e (f * g) =
      fixedKernelLabel q hq K φ e f * fixedKernelLabel q hq K φ e g) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (H →ₐ[LocalRing q] K))
    (hNat : (e g).val.val = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e f).val.val),
fixedKernelLabel q hq K φ e g = σ • fixedKernelLabel q hq K φ e f) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (hMul : ∀ f g, (e (f * g)).val = (localLaw q hq).mul _ (e f).val (e g).val)
    (f g : WithConv (H →ₐ[LocalRing q] K)),
arithmeticKernelLabel q hq K φ e (f * g) =
      arithmeticKernelLabel q hq K φ e f + arithmeticKernelLabel q hq K φ e g) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] (e : WithConv (H →ₐ[LocalRing q] K) ≃ kernelPoints (localLaw q hq) (integralNorm q hq φ) (MazurTransfer.FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)), ∀ (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (H →ₐ[LocalRing q] K))
    (hNat : (e g).val.val = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e f).val.val),
arithmeticKernelLabel q hq K φ e g = σ • arithmeticKernelLabel q hq K φ e f) := by
  exact ⟨MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsProof20261020.fixedKernelLabel_mul, MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsProof20261020.fixedKernelLabel_act, MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsProof20261020.arithmeticKernelLabel_add, MazurTransfer.OriginalIntegralHopfArithmeticKernelLabelsProof20261020.arithmeticKernelLabel_act⟩
#print axioms solution
