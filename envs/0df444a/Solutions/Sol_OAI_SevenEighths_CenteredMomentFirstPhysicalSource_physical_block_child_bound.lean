-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstPhysicalSource.physical_block_child_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:49:05.29571+00:00
-- url     : https://prove2.me/submissions/e2341e08-0f0d-4dab-a983-3419b528fa9f

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstPhysicalSource_block_eq_whole

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

end EisensteinSchwartzPoisson

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (eisEmbedding z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_finite_character_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    exact zero_le_one

theorem finiteSexticRow_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    ‖finiteSexticRow P hg j a‖ ≤ 1 := by
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  rw [finiteSexticRow, norm_prod]
  calc
    _ ≤ ∏ i : ι, (1 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => norm_finite_character_le_one
        (canonicalSextic (P i) (hg i) ^ j i) _)
    _ = 1 := by simp

end QuadraticInitialBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

open FirstPassCubeLabels

lemma weighted_schwartz_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  simpa using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J

end JointLogSeparation

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Physical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

attribute [local irreducible] markedPhysicalProbe

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Mask
namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem ideal_coprime_mobius (I R : Ideal O) (hR : R ≠ 0) :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

end SevenEighths.CenteredMomentMask
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupportedCorrelation
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentCommonSupport

lemma sexticReciprocityPhase_symm (a b : O) :
    sexticReciprocityPhase a b = sexticReciprocityPhase b a := by
  exact congrArg (fun z : ℤ => (z : ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem supported_opposite_phase (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcop : IsCoprime a b) [Fintype (Residue a)] :
    idealRowHom a (Ideal.span {b}) * star (idealRowHom b (Ideal.span {a})) =
      sexticReciprocityPhase a b := by
  rw [idealRowHom_primary_reciprocity b a hpb hpa hb ha,
    sexticReciprocityPhase_symm b a, mul_assoc]
  have hunit := isUnit_residue_of_coprime a b hcop
  have hn := (supportedModulusCharacter a ha).apply_ne_zero_iff.mpr hunit
  change idealRowHom b (Ideal.span {a}) ≠ 0 at hn
  have heq : idealRowHom b (Ideal.span {a}) * star (idealRowHom b (Ideal.span {a})) = 1 := by
    change supportedModulusCharacter a ha (Ideal.Quotient.mk _ b) *
      star (supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)) = 1
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ hn
  rw [heq, mul_one]

end SevenEighths.CenteredMomentSupportedCorrelation
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Fourier
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

end SevenEighths.CenteredMomentFourier
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Smooth
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentSmooth
open FourierBridge EisensteinSchwartzPoisson

theorem whole_kernel_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
        ∫ t : ℝ, separatedKernel V ρ x u v t * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  let U : Fin 4 → ℝ → ℂ := ![V 0, V 1, rootWindow (V 2), rootWindow (V 3)]
  let a : Fin 4 → ℝ := ![1, 1, -1, -1]
  have hU : ∀ i y, U i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i
    · exact hV 0 y hy
    · exact hV 1 y hy
    · apply hV 2 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
    · apply hV 3 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W U a M hM hU A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  refine ⟨b, ?_, hi, hm, hp⟩
  intro ρ x u v
  have h := hb ![ρ, x, u, v]
  simpa [U, a, wholeKernel, separatedKernel, rowPhase, columnPhase,
    Fin.prod_univ_succ, Fin.sum_univ_succ, sub_eq_add_neg, mul_assoc, add_assoc] using h

lemma separated_integrable (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (ρ x u v : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => c * separatedKernel V ρ x u v t * b t) := by
  let K : ℝ := ‖c‖ * ‖V 0 ρ‖ * ‖V 1 x‖ * ‖rootWindow (V 2) u‖ * ‖rootWindow (V 3) v‖
  apply (b.integrable.norm.const_mul K).mono'
  · have hρ := logPhase_continuous_left ρ
    have hx := logPhase_continuous_left x
    have hu := logPhase_continuous_left (-u)
    have hv := logPhase_continuous_left (-v)
    exact (by unfold separatedKernel rowPhase columnPhase; fun_prop : Continuous (fun t : ℝ =>
      c * separatedKernel V ρ x u v t * b t)).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [separatedKernel, rowPhase, columnPhase, norm_mul, logPhase_norm, mul_one]
    dsimp only [K]
    ring_nf
    exact le_rfl

theorem finite_pair_separation {α β : Type*}
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
      ∫ t : ℝ, separatedKernel V ρ x u v t * b t)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
      ∫ t : ℝ, rowPhase V ρ x t *
        (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
        (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∫ t : ℝ,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsep, ← integral_const_mul]
      congr 1
      funext t
      ring
    _ = ∫ t : ℝ, ∑ i ∈ S, ∑ j ∈ T,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum T
        (fun j _ => separated_integrable b V ρ x (u i) (v j) (c i * star (d j))))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ =>
        separated_integrable b V ρ x (u i) (v j) (c i * star (d j)))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [Finset.sum_mul, Finset.mul_sum, separatedKernel]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem whole_product_pair_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ {α β : Type*} (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
        (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ),
        (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
          ∫ t : ℝ, rowPhase V ρ x t *
            (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
            (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hs⟩ := whole_kernel_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  exact ⟨b, fun S T c d u v ρ x => finite_pair_separation W V R b hb S T c d u v ρ x,
    hi, hm, hp⟩

open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentSmooth
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Cauchy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentCauchy
open CenteredMomentSmooth FourierBridge

theorem bounded_row_cauchy {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀ k ∈ rows, ‖w k‖ ≤ 1) :
    ‖∑ k ∈ rows, w k * A k * B k‖ ≤
      Real.sqrt (∑ k ∈ rows, ‖A k‖ ^ 2) * Real.sqrt (∑ k ∈ rows, ‖B k‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ rows, ‖w k * A k * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ rows, ‖A k‖ * ‖B k‖ := Finset.sum_le_sum fun k hk => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt rows _ _

lemma paired_columns_integrable {α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (ρ x : ℝ)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => z * (rowPhase V ρ x t *
      leftColumn S c (V 2) u t * rightColumn T d (V 3) v t * b t)) := by
  have hi := integrable_finsetSum S (fun i _ => integrable_finsetSum T
    (fun j _ => separated_integrable b V ρ x (u i) (v j) (z * c i * star (d j))))
  convert (preTransparency := .instances) hi using 1
  funext t
  simp only [leftColumn, rightColumn, Finset.mul_sum, Finset.sum_mul, separatedKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem common_density_cauchy {κ α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset κ) (S : Finset α) (T : Finset β)
    (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
    (ρ x : κ → ℝ) (η : κ → ℂ)
    (hη : ∀ k ∈ rows, ‖η k‖ ≤ 1)
    (hV₀ : ∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) (hV₁ : ∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1)
    (E : ℝ) (_hE : 0 ≤ E) (J : ℕ)
    (henergy : ∀ t : ℝ,
      Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) :
    ‖∑ k ∈ rows, η k * ∫ t : ℝ, rowPhase V (ρ k) (x k) t *
      leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t‖ ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hrow (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖η k * rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
    rw [norm_mul, rowPhase, norm_mul, norm_mul, norm_mul, logPhase_norm, logPhase_norm, mul_one, mul_one]
    exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
  have hpoint (t : ℝ) :
      ‖∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ ≤
        E * ((1 + ‖t‖) ^ J * ‖b t‖) := by
    have hs := bounded_row_cauchy rows (fun k => η k * rowPhase V (ρ k) (x k) t)
      (fun k => leftColumn S (c k) (V 2) u t) (fun k => rightColumn T (d k) (V 3) v t)
      (fun k hk => hrow k hk t)
    have he : (∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)) =
        (∑ k ∈ rows, (η k * rowPhase V (ρ k) (x k) t) *
          leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t) * b t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hs.trans (henergy t)) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) :=
    JointLogSeparation.weighted_schwartz_integrable b J
  calc
    _ = ‖∫ t : ℝ, ∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ := by
      congr 1
      rw [integral_finsetSum _ (fun k _ =>
        paired_columns_integrable b V (ρ k) (x k) S T (c k) (d k) u v (η k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ ≤ ∫ t : ℝ, E * ((1 + ‖t‖) ^ J * ‖b t‖) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

theorem whole_kernel_row_estimate (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (rows : Finset κ) (S : Finset α) (T : Finset β)
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) →
      (1 + R) ^ A * ‖∑ k ∈ rows, η k *
        (∑ i ∈ S, ∑ j ∈ T, (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u i) (v j))‖ ≤ C * E := by
  obtain ⟨C, hC, hs⟩ := whole_product_pair_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β rows S T c d u v ρ x η hη hV₀ hV₁ E hE he
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  have hid (k : κ) := hb S T (c k) (d k) u v (ρ k) (x k)
  simp_rw [hid]
  have hcs := common_density_cauchy b V rows S T c d u v ρ x η hη hV₀ hV₁ E hE J he
  change (1 + R) ^ A * ‖∑ k ∈ rows, η k * ∫ t : ℝ,
    rowPhase V (ρ k) (x k) t * leftColumn S (c k) (V 2) u t *
      rightColumn T (d k) (V 3) v t * b t‖ ≤ _
  calc
    _ ≤ (1 + R) ^ A * (E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = E * ((1 + R) ^ A * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_left hm hE
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentCauchy
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FixedRay
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open RayFourExpansion CenteredMomentPrimary HeckeFamily HeckeRowClosure
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_rayMask (a : O) (ha : Supported (Ideal.span {a})) : rayMask a = 1 := by
  rw [rayMask, if_pos (CenteredMomentCommonSupport.isUnit_residue_of_coprime
    4 a (supported_coprime_four a ha))]

end SevenEighths.CenteredMomentFixedRay

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.MobiusRegroup
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentMobiusRegroup
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

theorem mobius_on_pool {β : Type*} (T : Finset β) (B : β → Ideal O)
    (hB : ∀ j ∈ T, B j ≠ 0) (j : β) (hj : j ∈ T) (I : Ideal O) :
    (if IsCoprime I (B j) then (1 : ℂ) else 0) =
      ∑ D ∈ divisorPool T B, if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
  rw [ideal_coprime_mobius I (B j) (hB j hj)]
  have hsub : idealDivisors (B j) ⊆ divisorPool T B :=
    fun D hD => Finset.mem_biUnion.mpr ⟨j,hj,hD⟩
  calc
    _ = ∑ D ∈ idealDivisors (B j), if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [(mem_idealDivisors (hB j hj)).mp hD, and_true]
    _ = _ := Finset.sum_subset hsub (by
      intro D hD hn
      have hnd : ¬ D ∣ B j := fun hd => hn ((mem_idealDivisors (hB j hj)).mpr hd)
      simp only [hnd, and_false, ite_false])

theorem finite_pair_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Ideal O) (B : β → Ideal O) (hB : ∀ j ∈ T, B j ≠ 0)
    (F : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if IsCoprime (A i) (B j) then F i j else 0) =
      ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T, if D ∣ A i ∧ D ∣ B j then F i j else 0 := by
  have ht (i : α) (j : β) (hj : j ∈ T) :
      (if IsCoprime (A i) (B j) then F i j else 0) =
        ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
          (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
    have hm := congrArg (fun z : ℂ => z * F i j) (mobius_on_pool T B hB j hj (A i))
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_mul, mul_ite, mul_zero] using hm
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact ht i j hj
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := divisorPool T B)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      simp only [Finset.mul_sum]

open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentMobiusRegroup

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ChildAssembly
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentMobiusRegroup CenteredMomentRowNorm RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem rayCharacter_inverse_star (χ : RayCharacter) (a : O) :
    star (rayCharacter (χ⁻¹) a) = rayCharacter χ a := by
  change star ((χ⁻¹) (Ideal.Quotient.mk _ a)) = χ (Ideal.Quotient.mk _ a)
  rw [MulChar.star_apply', inv_inv]

theorem pair_ray_fubini {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (S : Finset α) (T : Finset β) (A : γ → δ → ℂ)
    (L : α → γ → ℂ) (R : β → δ → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, ∑ χ : γ, ∑ ξ : δ, A χ ξ * (L i χ * R j ξ) * K i j) =
      ∑ χ : γ, ∑ ξ : δ, A χ ξ * ∑ i ∈ S, ∑ j ∈ T, (L i χ * R j ξ) * K i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := S)]
  simp_rw [Finset.sum_comm (s := S) (t := Finset.univ)]
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end SevenEighths.CenteredMomentChildAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.GaussEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentGaussEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentFourier
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem gaussRow_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

theorem gaussPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gaussEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  exact (hasSum_sum (fun i _ =>
    (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (gaussEnergy S a ha c W K).re at hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2 *
        (W (‖eisEmbedding z‖ ^ 2 / K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ChildEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem leftColumn_eq_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      gaussPolynomial S a ha (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      star (gaussPolynomial S a ha (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, gaussPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SevenEighths.CenteredMomentChildEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstColumns
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstColumns
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

theorem first_phase_columns (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hpb : ConcretePrimeRowBridge.goodLambda^2∣b-1) (hab : IsCoprime a b) :
    (idealRowHom e (Ideal.span {a})*star (idealRowHom e (Ideal.span {b}))*ρ e)*
      (idealRowHom (b*r) (Ideal.span {a})*star (idealRowHom (a*r) (Ideal.span {b}))*ρ (a*b)) =
      ρ e*sexticReciprocityPhase a b*leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let : Fintype (CenteredMomentCommonSupport.Residue a) := Fintype.ofFinite _
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let : Fintype (CenteredMomentCommonSupport.Residue b) := Fintype.ofFinite _
  have hp := supported_opposite_phase b a hb ha hpb hpa hab.symm
  rw [sexticReciprocityPhase_symm b a] at hp
  calc
    _ = ρ e*(idealRowHom b (Ideal.span {a})*star (idealRowHom a (Ideal.span {b})))*
        leftCoefficient e r ρ a*star (rightCoefficient e r ρ b) := by
      simp only [leftCoefficient,rightCoefficient,idealRowHom_argument_mul,hρ,star_mul,star_star]
      ring
    _ = _ := by rw [hp]

theorem firstPhaseTable_mk (a b : O) :
    firstPhaseTable (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)=sexticReciprocityPhase a b := by
  simp only [firstPhaseTable,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem firstPhaseTable_expansion (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a b=∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*rayCharacter χ a*rayCharacter ξ b := by
  have hh := pair_phase_expansion firstPhaseTable a b
  simpa only [supported_rayMask a ha,supported_rayMask b hb,one_mul,firstPhaseTable_mk] using hh

theorem firstPhaseTable_mass :
    (∑ χ : RayCharacter,∑ ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)≤256 := by
  have hb : ∀ u v : RayRingˣ,‖firstPhaseTable u v‖≤1 := by
    intro u v
    unfold firstPhaseTable QuadraticAllOddCRT.quadraticRaySign
    split_ifs <;> norm_num
  simpa only [mul_one] using pairCoeff_sum_norm_le firstPhaseTable 1 hb

theorem firstExtension_separated (e r a b : O) (ρ : O → ℂ)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    firstExtension e r ρ a b=ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*(leftCoefficient e r ρ a*rayCharacter χ a)*
        star (rightCoefficient e r ρ b*rayCharacter (ξ⁻¹) b) := by
  unfold firstExtension
  rw [firstPhaseTable_expansion a b ha hb]
  simp only [Finset.mul_sum,Finset.sum_mul,star_mul,CenteredMomentChildAssembly.rayCharacter_inverse_star]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  ring

end SevenEighths.CenteredMomentFirstColumns

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstAssembly
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstColumns CenteredMomentMobiusRegroup CenteredMomentChildAssembly
open CenteredMomentGaussEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem originalPhase_eq (e r a b : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hpb : ConcretePrimeRowBridge.goodLambda^2∣b-1) (hab : IsCoprime a b) :
    originalPhase e r ρ a b=firstExtension e r ρ a b :=
  first_phase_columns e r a b ρ hρ ha hb hpa hpb hab

theorem first_divisor_pair {α β : Type*} (L : Ideal O)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ) (h : O)
    (i : α) (j : β) (K : ℂ) :
    (if L∣Ideal.span {a i} ∧ L∣Ideal.span {b j} then
      firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K else 0) =
    ρ e*∑ χ : RayCharacter,∑ ξ : RayCharacter,
      pairCoeff firstPhaseTable χ ξ*
        ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
          star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
            gaussRow (b j) (hb j) (-h)))*K := by
  by_cases hi : L∣Ideal.span {a i}
  · by_cases hj : L∣Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [firstExtension_separated e r (a i) (b j) ρ (ha i) (hb j)]
      simp only [Finset.mul_sum,Finset.sum_mul,star_mul,rayCharacter_inverse_star]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,mul_zero,Finset.sum_const_zero]

theorem finite_first_children {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (h : O) (K : α → β → ℂ) :
    (∑ i∈S,∑ j∈T,(if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
      (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j) =
    ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
      (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
        ∑ χ : RayCharacter,∑ ξ : RayCharacter,
          pairCoeff firstPhaseTable χ ξ*∑ i∈S,∑ j∈T,
            ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) h)*
              star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                gaussRow (b j) (hb j) (-h)))*K i j := by
  have ht (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*
        (c i*star (d j))*(gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        firstExtension e r ρ (a i) (b j)*(c i*star (d j))*
          (gaussRow (a i) (ha i) h*star (gaussRow (b j) (hb j) (-h)))*K i j else 0 := by
    rw [Ideal.isCoprime_span_singleton_iff]
    by_cases hc : IsCoprime (a i) (b j)
    · simp only [hc,ite_true,originalPhase_eq e r (a i) (b j) ρ hρ (ha i) (hb j) (hpa i) (hpb j) hc]
    · simp only [hc,ite_false,zero_mul]
  simp_rw [ht]
  rw [finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1)]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [first_divisor_pair L a b ha hb c d e r ρ h]
  simp_rw [← Finset.mul_sum (s:=T),← Finset.mul_sum (s:=S)]
  rw [pair_ray_fubini]
  ring

end SevenEighths.CenteredMomentFirstAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedChild
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentReflectedChild
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth CenteredMomentChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem finite_reflected_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c (-z)‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hh := finite_energy_le_gaussEnergy S a ha c W K hK (rows.image Neg.neg) hW
    (by intro z hz;obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rw [Finset.sum_image] at hh
  · exact hh
  · intro x hx y hy hxy
    exact neg_injective hxy

theorem whole_kernel_reflected_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) (-z))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) (-z)) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_reflected_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentReflectedChild

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstChildBound
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildBound
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentReflectedChild
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem finite_first_ray_divisor_bound (L : Finset (Ideal O))
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (firstPhaseTable) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (firstPhaseTable_mass)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert (preTransparency := .instances) h using 1 ; ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert (preTransparency := .instances) h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem first_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (q : O → ℂ) (K : O → α → β → ℂ) :
    (∑ z∈rows,q z*∑ i∈S,∑ j∈T,
      ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
        (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*K z i j)=
      ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            ∑ z∈rows,(q z*ρ e)*∑ i∈S,∑ j∈T,
              ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) z)*
                star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                  gaussRow (b j) (hb j) (-z)))*K z i j := by
  simp_rw [finite_first_children S T a b ha hb hpa hpb c d e r ρ hρ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem whole_kernel_first_child_bound (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i,0≤M i)
    (hV : ∀ i y,V i y≠0 → |y|≤M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ R : ℝ,0<R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j})),
      (∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1) →
      (∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1) →
      ∀ (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ),
      (∀ x y,ρ (x*y)=ρ x*ρ y) → ‖ρ e‖≤1 →
      ∀ (q : O → ℂ) (u : α → ℝ) (v : β → ℝ) (ρ₀ x : O → ℝ),
      (∀ z∈rows,‖q z‖≤1) →
      (∀ z∈rows,‖V 0 (ρ₀ z)‖≤1) → (∀ z∈rows,‖V 1 (x z)‖≤1) →
      ∀ (U : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₁ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₂ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ χ : RayCharacter,∀ t : ℝ,
        (gaussEnergy S a ha (fun i =>
          divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
            columnPhase (V 2) (u i) t) U K).re≤(B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ ξ : RayCharacter,∀ t : ℝ,
        (gaussEnergy T b hb (fun j =>
          divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) ξ j*
            star (columnPhase (V 3) (v j) t)) U K).re≤(B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A*‖∑ z∈rows,q z*∑ i∈S,∑ j∈T,
        ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
          (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*
            wholeKernel W V R (ρ₀ z) (x z) (u i) (v j)‖≤
        C*∑ L∈divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_reflected_gauss_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T a b ha hb hpa hpb c d e r ρ hρ hρe q u v ρ₀ x hq hV₀ hV₁ U K hK hU hmajor
    B₁ B₂ hB₁ hB₂ hleft hright
  rw [first_row_children rows S T a b ha hb hpa hpb c d e r ρ hρ]
  apply finite_first_ray_divisor_bound _ _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ)
    (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹))
    u v ρ₀ x (fun z => q z*ρ e)
    (fun z hz => by rw [norm_mul];exact (mul_le_of_le_one_left (norm_nonneg _) (hq z hz)).trans hρe)
    hV₀ hV₁ U K hK hU hmajor (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL)
    (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentFirstChildBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentPrimitive IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

lemma element_primary (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    goodLambda^2∣element C D hD S a-1:=
  (CompletedGauss.primaryGenerator_spec a (supported_primaryGenerator_ne_zero a
    (column_supported C D hD S a))).2

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceBound
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentFirstReduced
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentFirstChildBound CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentSmooth RayFourExpansion IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem physical_block_child_bound_oai (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (M:Fin 4→ℝ)(hM:∀i,0≤M i)(hV:∀i y,V i y≠0→|y|≤M i)(A J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤Cbound ∧
    ∀(η:Character)(m:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
      (C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0<K→0<K₀→0<H₀→0<A₀→0<B₀→
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let k:=K/‖eisEmbedding e‖^2;
    let r:=activeConductor C D;
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D);
    (∀h∈rows,‖V 0 (Real.log ((k/‖eisEmbedding r‖^2)/K₀))‖≤1)→
    (∀h∈rows,‖V 1 (Real.log (‖eisEmbedding h‖^2/H₀))‖≤1)→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0<H→
    (∀h:O,0≤(U (‖eisEmbedding h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖eisEmbedding h‖^2/H)).re)→
    ∀B₁ B₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),0≤B₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),0≤B₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C C hC.1 S) (element_supported C C hC.1 S)
        (fun a=>divisorCoefficient L (element C C hC.1 S)
          (fun a=>coefficient η m 1 t c C a*leftCoefficient e r ρ (element C C hC.1 S a)) χ a*
          columnPhase (V 2) (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀)) v) U H).re
            ≤(B₁ L*(1+‖v‖)^J₁)^2)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C D hD.1 S) (element_supported C D hD.1 S)
        (fun b=>divisorCoefficient L (element C D hD.1 S)
          (fun b=>coefficient η m 1 t c D b*rightCoefficient e r ρ (element C D hD.1 S b)) χ b*
          star (columnPhase (V 3) (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)) v)) U H).re
            ≤(B₂ L*(1+‖v‖)^J₂)^2)→
    (1+K₀*H₀/(A₀*B₀))^A*‖block η m 1 t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
          (fun b=>Ideal.span {element C D hD.1 S b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L):=by
  obtain ⟨Cbound,hCbound,hbound⟩:=whole_kernel_first_child_bound.{0,0} W V M hM hV A J₁ J₂
  refine ⟨Cbound,hCbound,?_⟩
  intro η m t S c C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  dsimp only
  intro hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  have hh:=hbound (K₀*H₀/(A₀*B₀)) (div_pos (mul_pos hK₀ hH₀) (mul_pos hA₀ hB₀))
    rows Finset.univ Finset.univ (element C C hC.1 S) (element C D hD.1 S)
    (element_supported C C hC.1 S) (element_supported C D hD.1 S)
    (element_primary C C hC.1 S) (element_primary C D hD.1 S)
    (fun a=>coefficient η m 1 t c C a) (fun b=>coefficient η m 1 t c D b)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (activeConductor C D)
    (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D))
    (finiteSexticRow_mul _ _ _) (QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _)
    (fun h=>star (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) h))
    (fun a=>Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
    (fun b=>Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀))
    (fun _=>Real.log ((K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2/
      ‖eisEmbedding (activeConductor C D)‖^2)/K₀))
    (fun h=>Real.log (‖eisEmbedding h‖^2/H₀))
    (fun h _=>by rw [norm_star];exact QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _)
    hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [block_eq_whole η m 1 t S c C D hC hD hCD E rows hrows W V K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀,
    norm_mul]
  convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hh (norm_nonneg (scalar C D hC E K A₀ B₀)) using 1 <;> ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentFirstPhysicalSource.physical_block_child_bound_oai := @OAI.SevenEighths.CenteredMomentFirstPhysicalSource.physical_block_child_bound_oai
