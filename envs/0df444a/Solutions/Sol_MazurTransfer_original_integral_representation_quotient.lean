-- Prove2me | solution 1 for MazurTransfer.original_integral_representation_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T07:06:33.727127+00:00
-- url     : https://prove2.me/submissions/9f60113b-d167-4ea9-b00b-a0176f517c06

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every same finite-flat arithmetic norm-kernel Hopf model admits a genuine bialgebra quotient extending the originally selected surjective intertwining map, with the original arithmetic labels and point restriction retained.
Named downstream consumer: same selected pi and conjugate-pi arithmetic character quotients at nineteen and their integral Kummer pushforwards.
-/
import Definitions.Def_MazurTransfer_OriginalIntegralRepresentationQuotientData20261020
import Definitions.Def_MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
import Theorems.Thm_MazurTransfer_original_actual_arithmetic_kernel_additive_action_laws
import Theorems.Thm_MazurTransfer_original_finite_flat_arithmetic_bialgebra_quotient
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardNormKernelGaloisAction MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open MazurTransfer.Order13ActualNormKernelF19Representation MazurTransfer.Order13ActualNormKernelFiniteModule
open MazurTransfer.Order13IntegralRepresentationQuotient
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13IntegralRepresentationQuotient.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient
attribute [local instance] MazurTransfer.Order13IntegralRepresentationQuotient.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient
attribute [local instance] MazurTransfer.Order13IntegralRepresentationQuotient.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralRepresentationQuotient
attribute [local instance] MazurTransfer.Order13IntegralRepresentationQuotient.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralRepresentationQuotient
attribute [local instance] MazurTransfer.Order13IntegralRepresentationQuotient.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralRepresentationQuotient
namespace MazurTransfer.OriginalIntegralRepresentationQuotientBoundary20261020
end MazurTransfer.OriginalIntegralRepresentationQuotientBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: extend a selected equivariant surjection from the SAME
arithmetic norm-kernel Hopf model to a finite-flat bialgebra quotient.
The arithmetic label and selected quotient are retained pointwise.
Named downstream consumer: the previously selected pi and conjugate-pi
character quotients at nineteen and their integral Kummer pushforwards.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralRepresentationQuotientProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardNormKernelGaloisAction Order13ActualArithmeticKernelAdditiveAction
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime]
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]


variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]



variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (ρ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (p : Representation.IntertwiningMap (kernelRepresentation K φ) ρ)





theorem every_arithmetic_model_has_quotient (hp : Function.Surjective p) :
    EveryArithmeticModelHasQuotient q K φ ρ p := by
  intro G iCR iHA hFin hFlat hComm e he_add he_act
  letI : DistribMulAction (K ≃ₐ[ℚ] K) V :=
    RepresentationCanonicalDistribMulAction.ofRepresentation ρ
  have hp_act : ∀ (σ : K ≃ₐ[ℚ] K) (m : Additive (Kernel K φ)),
      p (σ • m) = σ • p m := by
    intro σ m
    change p (σ • m) = ρ σ (p m)
    rw [(MazurTransfer.original_actual_arithmetic_kernel_additive_action_laws).2 K φ σ m]
    exact Representation.IntertwiningMap.isIntertwining _ _ p σ m
  have hfix : ∀ c : K, (∀ σ : K ≃ₐ[ℚ] K, σ c = c) →
      c ∈ Set.range (algebraMap ℚ K) := by
    intro c hc
    exact (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (K := K) c).mpr hc
  exact MazurTransfer.original_finite_flat_arithmetic_bialgebra_quotient
    (F := ℚ) e he_add he_act p.toLinearMap.toAddMonoidHom hp hp_act hfix

end MazurTransfer.OriginalIntegralRepresentationQuotientProof20261020

theorem solution : ∀ (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
  [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
  (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
  [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
  {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
  (ρ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) ρ)
  (hp : Function.Surjective p), EveryArithmeticModelHasQuotient q K φ ρ p := by
  exact MazurTransfer.OriginalIntegralRepresentationQuotientProof20261020.every_arithmetic_model_has_quotient
#print axioms solution
