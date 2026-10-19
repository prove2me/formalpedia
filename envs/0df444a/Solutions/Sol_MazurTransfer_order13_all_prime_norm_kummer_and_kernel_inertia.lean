-- Prove2me | solution 1 for MazurTransfer.order13_all_prime_norm_kummer_and_kernel_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T11:40:48.708257+00:00
-- url     : https://prove2.me/submissions/a45d0c20-f613-449e-a40b-c140b911e485

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual norm maps and kernel actions are unramified on genuine valuation inertia at every prime except 13 and 19, including 2.
Named downstream consumer: actual character local conditions, Selmer bounds and rank zero.
-/
import Definitions.Def_MazurTransfer_Order13OriginalAllPrimeNormKummerTopologyAndInertiaNormalClosureData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_continuous_norm_kummer_and_fixed_quotient_unramified
import Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_norm_lift_inertia_fixed
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestriction_restrictedClass_zero_iff_subgroup_invariant_preimage
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualNormKernelF19Representation
open Order13ActualNormKernelAwayThirteenNineteenInertia
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instTopologicalSpacePoints_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instDiscreteTopologyPoints_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instMulActionAlgEquivRatPoints_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKernelAwayThirteenNineteenInertia
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKernelAwayThirteenNineteenInertia
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormKernelAwayThirteenNineteenInertia
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instNormalAlgEquivRatInertiaAwayThirteenNineteenNormalSubgroup
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualNormKernelAwayThirteenNineteenInertia
namespace MazurTransfer.AllPrimeNormKummerProofBoundary20261019
end MazurTransfer.AllPrimeNormKummerProofBoundary20261019
namespace MazurTransfer.AllPrimeNormArithmeticProof20261019

theorem not_dvd_104_of_prime_ne_two_thirteen (q : ℕ) [Fact q.Prime]
    (h2 : q ≠ 2) (h13 : q ≠ 13) : ¬ (q : ℤ) ∣ 104 := by
  intro h
  have hp : q.Prime := Fact.out
  have hn : q ∣ 104 := Int.natCast_dvd_natCast.mp h
  have hm : q ∣ 2 ^ 3 * 13 := by norm_num at hn ⊢; exact hn
  rcases hp.dvd_mul.mp hm with h | h
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h))
  · exact h13 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)

end MazurTransfer.AllPrimeNormArithmeticProof20261019

namespace MazurTransfer.AllPrimeDyadicNormLiftBridge20261019
theorem norm_lift_inertia_fixed (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    actionHom K σ b = b :=
  MazurTransfer.order13_actual_dyadic_continuous_norm_kummer_and_fixed_quotient_unramified.1 K φ hφ A hA a b hb σ hσ
end MazurTransfer.AllPrimeDyadicNormLiftBridge20261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME actual rational norm lifts and continuous
Kummer classes are unramified at every prime except thirteen and nineteen.
The dyadic case uses the actual mixed integral model; all remaining
primes use the existing actual good-prime models in a common environment.
Named downstream consumer: actual character Selmer images and rank zero.
-/

noncomputable section
namespace MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKummerAwayThirteenNineteen
open Order13ActualNormKummerAwayThirteenNineteen
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKummerAwayThirteenNineteen

variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
include h13 h19

theorem norm_lift_inertia_fixed (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    actionHom K σ b = b := by
  by_cases h2 : q = 2
  · subst q
    exact MazurTransfer.AllPrimeDyadicNormLiftBridge20261019.norm_lift_inertia_fixed K φ hφ A hA a b hb σ hσ
  · exact Order13GoodPrimeUnramifiedKummer.norm_lift_inertia_fixed q
      (MazurTransfer.AllPrimeNormArithmeticProof20261019.not_dvd_104_of_prime_ne_two_thirteen q h2 h13)
      h19 K φ hφ A hA a b hb σ hσ

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable [IsGalois ℚ K]

attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instTopologicalSpacePoints_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instDiscreteTopologyPoints_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instMulActionAlgEquivRatPoints_order13ActualNormKummerAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormKummerAwayThirteenNineteen
open Order13ActualPicardNormAlgebraicCohomology Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
attribute [local instance] MazurTransfer.Order13ActualNormKummerAwayThirteenNineteen.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormKummerAwayThirteenNineteen
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormSubgroupRestriction

theorem continuous_norm_class_unramified
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0 := by
  apply (restrictedClass_zero_iff_subgroup_invariant_preimage K φ
    (A.inertiaSubgroupIn ℚ) a b hb).mpr
  exact ⟨b, hb, fun σ => norm_lift_inertia_fixed K φ q h13 h19 hφ A hA a b hb σ.val σ.property⟩

end MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKummerAwayThirteenNineteen

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual norm kernel Galois representations factor
through the algebraic quotient by all valuation inertia away from thirteen
and nineteen. No topological quotient identification or splitting is assumed.
Named downstream consumer: actual ordered character Selmer bounds.
-/

noncomputable section
namespace MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKernelAwayThirteenNineteenInertia
open Order13ActualNormKernelAwayThirteenNineteenInertia
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKernelAwayThirteenNineteenInertia
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormKernelAwayThirteenNineteenInertia

variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
open Order13ActualPicardNormKernelGaloisAction
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormKernelAwayThirteenNineteenInertia

theorem kernel_inertia_fixed
    (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (z : Kernel K φ) :
    σ • z = z := by
  have hr : rationalPoint K (1 : RationalPoints) = 1 := MonObj.comp_one _
  have hz : z.val ≫ φ = rationalPoint K (1 : RationalPoints) := z.property.trans hr.symm
  apply Subtype.ext
  exact AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKummerAwayThirteenNineteen.norm_lift_inertia_fixed K φ q h13 h19
    hφ A hA 1 z.val hz σ hσ

variable [IsGalois ℚ K]
open Order13ActualPicardNormAlgebraicCohomology

theorem kernel_rep_inertia_identity
    (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (kernelRep K φ).ρ σ = 1 := by
  apply LinearMap.ext
  intro z
  exact congrArg Additive.ofMul
    (kernel_inertia_fixed K φ q h13 h19 hφ A hA σ hσ z.toMul)





attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instNormalAlgEquivRatInertiaAwayThirteenNineteenNormalSubgroup

theorem inertiaNormalSubgroup_le_kernel
    (hφ : φ = schemePi ∨ φ = schemePiConjugate) :
    inertiaAwayThirteenNineteenNormalSubgroup K ≤ (kernelRep K φ).ρ.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro σ ⟨q, hp, h13, h19, A, hA, hσ⟩
  letI : Fact q.Prime := ⟨hp⟩
  exact kernel_rep_inertia_identity K φ q h13 h19 hφ A hA σ hσ





open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
attribute [local instance] MazurTransfer.Order13ActualNormKernelAwayThirteenNineteenInertia.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualNormKernelAwayThirteenNineteenInertia

theorem inertia_le_F19_representation_kernel
    (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q) :
    A.inertiaSubgroupIn ℚ ≤ (kernelRepresentation K φ).ker := by
  intro σ hσ
  exact (representation_kernel_iff K φ σ).mpr
    (fun z => kernel_inertia_fixed K φ q h13 h19 hφ A hA σ hσ z)

end MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKernelAwayThirteenNineteenInertia

end

theorem solution : (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19), ∀ (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ), actionHom K σ b = b) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19) [IsGalois ℚ K] [IsFinite φ.left], ∀ (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a), restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (z : Kernel K φ), σ • z = z) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsGalois ℚ K], ∀ (hφ : φ = schemePi ∨ φ = schemePiConjugate), inertiaAwayThirteenNineteenNormalSubgroup K ≤ (kernelRep K φ).ρ.ker) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsGalois ℚ K] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)], ∀ (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q), A.inertiaSubgroupIn ℚ ≤ (kernelRepresentation K φ).ker) := by
  exact ⟨MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKummerAwayThirteenNineteen.norm_lift_inertia_fixed, MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKummerAwayThirteenNineteen.continuous_norm_class_unramified, MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKernelAwayThirteenNineteenInertia.kernel_inertia_fixed, MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKernelAwayThirteenNineteenInertia.inertiaNormalSubgroup_le_kernel, MazurTransfer.AllPrimeNormKummerTheoremBody20261019.Order13ActualNormKernelAwayThirteenNineteenInertia.inertia_le_F19_representation_kernel⟩
#print axioms solution
