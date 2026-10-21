-- Prove2me | solution 1 for MazurTransfer.original_actual_arithmetic_kernel_additive_action_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T03:38:19.294895+00:00
-- url     : https://prove2.me/submissions/7dbe71a7-141c-471d-bff7-f2898720d6c5

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: express the existing arithmetic kernel action on its additive type tag and compare it pointwise with the previously fixed F19 representation.
Named downstream consumer: actual integral Hopf character quotient APIs.
-/
import Definitions.Def_MazurTransfer_OriginalActualArithmeticKernelAdditiveActionData20261020
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction MazurTransfer.Order13ActualNormKernelF19Representation
open MazurTransfer.Order13ActualNormKernelFiniteModule MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction
attribute [local instance] MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction
namespace MazurTransfer.OriginalActualArithmeticKernelAdditiveActionBoundary20261020
end MazurTransfer.OriginalActualArithmeticKernelAdditiveActionBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: express the EXISTING arithmetic kernel action on its
additive type tag, and check pointwise equality with the PREVIOUSLY FIXED
F19 representation. No new geometric or transported Galois action.
Named downstream consumer: actual integral Hopf character quotient APIs.
-/

noncomputable section
namespace MazurTransfer.OriginalActualArithmeticKernelAdditiveActionProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelF19Representation
open Order13ActualNormKernelFiniteModule
open scoped CategoryTheory.MonObj
variable (K : Type) [Field K] [CharZero K]


variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]






theorem kernelAdditiveAction_smul (σ : K ≃ₐ[ℚ] K) (z : Kernel K φ) :
    σ • Additive.ofMul z = Additive.ofMul (σ • z) := rfl

theorem kernelAdditiveAction_eq_fixed_representation [IsGalois ℚ K] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] (σ : K ≃ₐ[ℚ] K) (z : Additive (Kernel K φ)) :
    σ • z = kernelRepresentation K φ σ z := rfl

end MazurTransfer.OriginalActualArithmeticKernelAdditiveActionProof20261020

theorem solution : (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (σ : K ≃ₐ[ℚ] K) (z : Kernel K φ),
σ • Additive.ofMul z = Additive.ofMul (σ • z)) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ [IsGalois ℚ K] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] (σ : K ≃ₐ[ℚ] K) (z : Additive (Kernel K φ)),
σ • z = kernelRepresentation K φ σ z) := by
  exact ⟨MazurTransfer.OriginalActualArithmeticKernelAdditiveActionProof20261020.kernelAdditiveAction_smul, MazurTransfer.OriginalActualArithmeticKernelAdditiveActionProof20261020.kernelAdditiveAction_eq_fixed_representation⟩
#print axioms solution
