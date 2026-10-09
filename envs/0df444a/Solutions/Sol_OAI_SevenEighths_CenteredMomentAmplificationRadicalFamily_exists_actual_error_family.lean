-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentAmplificationRadicalFamily.exists_actual_error_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:35.60634+00:00
-- url     : https://prove2.me/submissions/be85c50d-b5ec-474c-874e-5fb8585f84de

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
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

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]

attribute [local instance] OAI.FiniteRayExpansion.instFintypeMulCharComplex_definitions
theorem zeroExtendUnits_fourier (f : Rˣ → ℂ) (r : R) :
    zeroExtendUnits f r = ∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [zeroExtendUnits_unit]
    exact (unit_fourier_inversion f u).symm
  · rw [zeroExtendUnits_nonunit f r hr]
    simp only [MulChar.map_nonunit _ hr, mul_zero, Finset.sum_const_zero]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

theorem rayCharacter_card_le : Fintype.card RayCharacter ≤ 16 := by
  rw [character_card_eq_units]
  exact rayUnit_card_le

theorem phase_expansion (f : RayRing → ℂ) (a : O) :
    rayMask a * f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayCharacter χ a := by
  rw [rayMask, ← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _

theorem phaseCoeff_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) (χ : RayCharacter) :
    ‖phaseCoeff f χ‖ ≤ B := unitFourierCoeff_norm_le _ B hf χ

end RayFourExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open FirstPassCubeLabels hiding O

theorem rowTwist_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z n : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z n =
      rowTwist Ψ m f 1 n * idealRowHom z (Ideal.span {n}) := by
  change Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (Ψ n * idealRowHom (m^6*f^4*1) (Ideal.span {n})) * idealRowHom z (Ideal.span {n})
  rw [mul_one,idealRowHom_argument_mul]
  ring

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

end CanonicalRowCompletion

open scoped BigOperators Classical
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open EisensteinEPrimaryPhase (Coord odd)

lemma quadraticRaySign_sq (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRaySign r s^2=1 := by
  unfold quadraticRaySign
  rw [if_pos ⟨hr,hs⟩]
  split_ifs <;> norm_num

end QuadraticAllOddCRT

open scoped BigOperators Classical

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Operations
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem elementCoeff_power_of_unit (χ : Character) (n : ℕ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk χ.modulus z)) :
    elementCoeff (χ.power n) z = elementCoeff χ z ^ n := by
  change (χ.residue ^ n) (Ideal.Quotient.mk χ.modulus z) = _
  obtain ⟨u, hu⟩ := hz
  rw [← hu, MulChar.pow_apply_coe, hu]
  rfl

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Twist
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

end SevenEighths.CenteredMomentTwist
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

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AddedZero
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAddedZero
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentRowNorm CenteredMomentFourier CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentGaussEnergy CenteredMomentZeroMode
open CenteredExceptionalCount CenteredMomentRectangle
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : O)}) := by
  simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using supported_one_ideal

end SevenEighths.CenteredMomentAddedZero

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationShortening
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationShortening
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentAmplificationLocal CenteredMomentAmplificationGlobal
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem supported_phase_sq (p u : O) (hp : Supported (Ideal.span {p}))
    (hu : Supported (Ideal.span {u})) : sexticReciprocityPhase p u ^ 2 = 1 := by
  unfold sexticReciprocityPhase
  exact_mod_cast QuadraticAllOddCRT.quadraticRaySign_sq _ _
    (supported_residue_odd p hp) (supported_residue_odd u hu)

theorem residualCharacter_moving (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1) :
    residualCharacter p k u = sexticReciprocityPhase p u ^ k *
      idealRowHom (p^(2*k)) (Ideal.span {u}) := by
  rw [residualCharacter,idealRowHom_argument_pow p (2*k) _ hu,
    idealRowHom_primary_reciprocity p u hpp hup hp hu,mul_pow,
    pow_mul,supported_phase_sq p u hp hu,one_pow,one_mul]

end SevenEighths.CenteredMomentAmplificationShortening

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ChildRows
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildRows
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily HeckeRowClosure
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem childCharacter_primary (η : Character) (χ : RayCharacter) (n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    elementCoeff (childCharacter η χ) n = elementCoeff η n * rayCharacter χ n := by
  rw [childCharacter, elementCoeff_product, primaryRayCharacter_primary χ n hn hp]

end SevenEighths.CenteredMomentChildRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationSourceDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourceDomain
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem residualIdeal_supported (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dif_pos hI]
  exact primeRemainder_supported p hp (primaryGenerator I)
    (by rw [primary_span_supported I hI];exact hI)

theorem valuationColumns_supported (S : Finset (Ideal O)) (p : O) (k : ℕ)
    (I : Ideal O) (hI : I∈valuationColumns S p k) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem residualColumns_supported (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (I : Ideal O) (hI : I∈residualColumns S p hp k) : Supported I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_supported p hp J (valuationColumns_supported S p k J hJ)

end SevenEighths.CenteredMomentAmplificationSourceDomain

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePool
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePool
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceDomain
open CenteredMomentSourceRow CenteredMomentLiveDomain CenteredMomentFirstSectors
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem residualIdeal_coprime (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    IsCoprime (Ideal.span {p}) (residualIdeal p hp I) := by
  rw [residualIdeal,dif_pos hI,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr
    (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).2

end SevenEighths.CenteredMomentAmplificationSourcePool

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSmoothedWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem gaussEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖gaussPolynomial S a ha c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (gaussEnergy S a ha c U K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c U K hK).hasSum
  simpa only [gaussEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

theorem finite_weighted_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (gaussEnergy S a ha c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (gaussEnergy_hasSum_re S a ha c U K hK)

end SevenEighths.CenteredMomentSmoothedWindowEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceAllocationEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceAllocationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

 theorem gaussPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*gaussPolynomial S a ha (d B) z := by
  simp only [gaussPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentSourceAllocationEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SourceSmoothedAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceSmoothedAllocation
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSourceAllocationEnergy CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

theorem smoothed_allocation_energy {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (gaussEnergy S a ha (fun i => ∑ B,b B*d B i) W K).re≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(gaussEnergy S a ha (d B) W K).re := by
  have hs := gaussEnergy_hasSum_re S a ha (fun i => ∑ B,b B*d B i) W K hK
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        (‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*gaussPolynomial S a ha (d B) z)) (hW z)
      rw [gaussPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using h
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        ∑ z∈rows,‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_gaussEnergy S a ha (d B) W K hK hW rows) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentSourceSmoothedAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.GaussNormalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentGaussNormalization
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentDivisorRawEnergy CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem sourceGaussEnergy_nonneg (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤(sourceGaussEnergy Q c f W K).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) (fun I : supportedColumns Q => c I*f I) W K hK
  change 0≤(gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

end SevenEighths.CenteredMomentGaussNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (norm_pos I hI)
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondChildProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly
open CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]

end SevenEighths.CenteredMomentSecondChildProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSecondChildProfile CenteredMomentSourceRow CenteredMomentChildRows
local notation "O" => ActualEisensteinCubic.O

theorem amplificationPhase_mk (p u : O) (k : ℕ) :
    amplificationPhase p k (Ideal.Quotient.mk _ u)=sexticReciprocityPhase p u^k := by
  simp only [amplificationPhase,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem amplificationPhase_norm (p : O) (k : ℕ) (r : RayRing) :
    ‖amplificationPhase p k r‖≤1 := by
  unfold amplificationPhase QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> cases k <;> simp

theorem amplificationPhase_expansion (p u : O) (k : ℕ)
    (hu : Supported (Ideal.span {u})) :
    sexticReciprocityPhase p u^k=
      ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*rayCharacter χ u := by
  have he := phase_expansion (amplificationPhase p k) u
  simpa only [supported_rayMask u hu,one_mul,amplificationPhase_mk] using he

theorem original_column_family (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (C I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
      rowWeight η m 1 1 t C *
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*(β (C*I)*heightCoeff (τ χ) t I) := by
  rw [map_mul]
  calc
    _ = rowWeight η m 1 1 t C *
      (β (C*I)*(rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I))) := by ring
    _ = _ := by rw [hτ I hI t,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro χ hχ;ring

end SevenEighths.CenteredMomentAmplificationFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationFamilyEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationFamilyEnergy
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRow CenteredMomentChildRows CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O

theorem amplification_family_energy (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (Q : Finset (Ideal O)) (C : Ideal O) (hC : C≠0) (β : Ideal O → ℂ) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
      (fun I => residualCharacter p k (primaryGenerator I)) W K).re≤
      16*∑ χ : RayCharacter,
        (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  let b : RayCharacter → ℂ := fun χ => rowWeight η m 1 1 t C*phaseCoeff (amplificationPhase p k) χ
  let d : RayCharacter → supportedColumns Q → ℂ := fun χ I => β (C*I)*heightCoeff (τ χ) t I
  have he (I : supportedColumns Q) :
      (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
        ∑ χ,b χ*d χ I := by
    rw [original_column_family η m p k τ hτ C I (Finset.mem_filter.mp I.property).2 β t,Finset.mul_sum]
    simp only [b,d,mul_assoc]
  have hb (χ : RayCharacter) : ‖b χ‖≤1 := by
    dsimp only [b]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m 1 1 t C hC)).trans
      (phaseCoeff_norm_le _ 1 (fun u => amplificationPhase_norm p k u) χ)
  have hd (χ : RayCharacter) : 0≤(sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re :=
    sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hh := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [funext he]
  apply hh.trans
  apply mul_le_mul
  · exact_mod_cast rayCharacter_card_le
  · apply Finset.sum_le_sum
    intro χ hχ
    apply mul_le_of_le_one_left (hd χ)
    nlinarith [hb χ,norm_nonneg (b χ)]
  · exact Finset.sum_nonneg (fun χ _ => mul_nonneg (sq_nonneg _) (hd χ))
  · norm_num

end SevenEighths.CenteredMomentAmplificationFamilyEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFactor
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFactor
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationShortening CenteredMomentSupportedCorrelation
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePool
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem residual_six_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 6 u=residualCharacter p 0 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,if_pos hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*(idealRowHom u (Ideal.span {p})^6)^2 := by ring
    _ = 1 := by rw [hphase,hx];norm_num
    _ = _ := by simp

theorem residual_seven_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 7 u=residualCharacter p 1 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,if_pos hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*sexticReciprocityPhase p u*
        (idealRowHom u (Ideal.span {p})^6)^2*idealRowHom u (Ideal.span {p})^2 := by ring
    _ = _ := by rw [hphase,hx];ring

theorem error_residual_factor (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    residualCharacter p (n+1) u=residualCharacter p (errorMovingExponent n) u := by
  rcases hn with rfl|rfl|rfl
  · rfl
  · exact residual_six_unit p u hp hu hcop
  · exact residual_seven_unit p u hp hu hcop

theorem residualColumns_coprime (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (k : ℕ) (I : Ideal O) (hI : I∈residualColumns S p hp k) :
    IsCoprime (Ideal.span {p}) I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_coprime p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (I : Ideal O) (hI : I∈residualColumns S p hp (n+1)) :
    residualCharacter p (n+1) (primaryGenerator I)=
      residualCharacter p (errorMovingExponent n) (primaryGenerator I) := by
  have hsI := residualColumns_supported S p hp (n+1) I hI
  apply error_residual_factor p _ hs _ _ n hn
  · rw [primary_span_supported I hsI];exact hsI
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [primary_span_supported I hsI]
    exact residualColumns_coprime S p hp (n+1) I hI

end SevenEighths.CenteredMomentAmplificationActiveFactor

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationFamilyEnergy CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem actual_error_energy_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K=
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (errorMovingExponent n) (primaryGenerator I)) W K := by
  let Q := residualColumns S p hp (n+1)
  apply congrArg (fun f : supportedColumns Q → ℂ =>
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) f W K)
  funext I
  dsimp only
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

end SevenEighths.CenteredMomentAmplificationActiveFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RadicalFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstFamily CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem elementCoeff_power_pos (χ : Character) (e : ℕ) (he : 0<e) (n : O) :
    elementCoeff (χ.power e) n=(elementCoeff χ n)^e := by
  by_cases hn : IsUnit (Ideal.Quotient.mk χ.modulus n)
  · exact elementCoeff_power_of_unit χ e n hn
  · have hz : elementCoeff χ n=0 := MulChar.map_nonunit _ hn
    have hp : elementCoeff (χ.power e) n=0 := MulChar.map_nonunit _ hn
    rw [hp,hz,zero_pow (Nat.ne_zero_of_lt he)]

theorem exists_product_presentation {ι : Type*} (S : Finset ι) (base : Character)
    (χ : ι→Character) (e : ι→ℕ) (he : ∀i∈S,0<e i)
    (M : Ideal O) (hb : M≤base.modulus) (hχ : ∀i∈S,M≤(χ i).modulus) :
    ∃τ : Character,M≤τ.modulus ∧ ∀n:O,
      elementCoeff τ n=elementCoeff base n*∏i∈S,(elementCoeff (χ i) n)^(e i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨base,hb,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨τ,hτ,ht⟩ := ih (fun i hi=>he i (Finset.mem_insert_of_mem hi))
      (fun i hi=>hχ i (Finset.mem_insert_of_mem hi))
    refine ⟨τ.product ((χ a).power (e a)),le_inf hτ (hχ a (Finset.mem_insert_self _ _)),?_⟩
    intro n
    rw [elementCoeff_product,elementCoeff_power_pos _ _ (he a (Finset.mem_insert_self _ _)),
      ht,Finset.prod_insert ha]
    ring

theorem single_row_on_base (η : Character) (m p n : O)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (hn : rowTwist (elementHom η) m 1 1 n≠0) :
    rowTwist (elementHom (η.power 0)) m 1 p n=idealRowHom p (Ideal.span {n}) := by
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  have hη : elementCoeff η n≠0 := left_ne_zero_of_mul hn
  have hunit := MulChar.apply_ne_zero_iff.mp hη
  have hp : elementCoeff (η.power 0) n=1 := by
    rw [elementCoeff_power_of_unit η 0 n hunit,pow_zero]
  have hm : IsCoprime m n := by
    by_contra h
    apply hn
    rw [rowTwist_extract_sixth_mask _ m 1 1 n hs]
    simp [coprimalityMask,h]
  rw [rowTwist_extract_sixth_mask _ m 1 p n hs]
  change elementCoeff (η.power 0) n*coprimalityMask m n*idealRowHom (1^4*p) _=_
  rw [hp,one_pow,one_mul]
  simp [coprimalityMask,hm]

theorem row_product_formula {ι : Type*} (S : Finset ι)
    (η : Character) (m : O) (p : ι→O) (e : ι→ℕ)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m) (n : O) :
    rowTwist (elementHom η) m 1 1 n*
      (∏i∈S,(rowTwist (elementHom (η.power 0)) m 1 (p i) n)^(e i))=
      rowTwist (elementHom η) m 1 (∏i∈S,(p i)^(e i)) n := by
  conv_rhs => rw [rowTwist_row_factor]
  by_cases hn : rowTwist (elementHom η) m 1 1 n=0
  · rw [hn,zero_mul,zero_mul]
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  congr 1
  simp_rw [single_row_on_base η m _ n hmLam hm2 hn]
  induction S using Finset.induction_on with
  | empty => simpa using (idealRowHom_one_supported (Ideal.span {n}) hs).symm
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,idealRowHom_argument_mul,
      idealRowHom_argument_pow _ _ _ hs,ih]

theorem exists_radical_row_presentation {ι : Type*} [Fintype ι]
    (η : Character) (m : O) (hm : m≠0) (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (p : ι→O) (hp : ∀i,Supported (Ideal.span {p i}))
    (e : ι→ℕ) (he : ∀i,0<e i) :
    ∃τ : Character,
      η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤τ.modulus ∧
      τ.modulus.absNorm≤η.modulus.absNorm*(Ideal.span {m}).absNorm*
        (Ideal.span {(72:O)}).absNorm*∏i,(Ideal.span {p i}).absNorm ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (∏i,(p i)^(e i)) n := by
  obtain ⟨base,hbase,hbasec⟩ := exists_supported_row_presentation η m 1 hm
    CenteredMomentAddedZero.supported_one_element hmLam hm2
  choose χ hχ hc using fun i=>exists_supported_row_presentation (η.power 0) m (p i) hm
    (hp i) hmLam hm2
  let B := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}
  let M := B*∏i,Ideal.span {p i}
  have hb : M≤base.modulus := by
    rw [hbase,Ideal.span_singleton_one,←Ideal.one_eq_top,mul_one]
    exact Ideal.mul_le_left
  have hch (i : ι) : M≤(χ i).modulus := by
    rw [hχ i]
    change B*(∏j,Ideal.span {p j})≤B*Ideal.span {p i}
    apply Ideal.dvd_iff_le.mp
    exact mul_dvd_mul_left B (Finset.dvd_prod_of_mem (fun j=>Ideal.span {p j}) (Finset.mem_univ i))
  obtain ⟨τ,hM,ht⟩ := exists_product_presentation Finset.univ base χ e (fun i _=>he i) M hb
    (fun i _=>hch i)
  have hMn : M≠0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (Finset.prod_ne_zero_iff.mpr (fun i _=>(hp i).1))
  refine ⟨τ,hM,?_,?_⟩
  · have hd : τ.modulus∣M := Ideal.dvd_iff_le.mpr hM
    have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hMn))
      (map_dvd Ideal.absNorm hd)
    simpa only [M,B,map_mul,map_prod] using hn
  · intro n
    rw [ht,hbasec]
    simp_rw [hc]
    exact row_product_formula Finset.univ η m p e hmLam hm2 n

end SevenEighths.CenteredMomentRadicalFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentAmplificationRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentRadicalFamily CenteredMomentFirstFamily
open CenteredMomentAmplificationFamily CenteredMomentAmplificationFamilyEnergy
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSecondChildProfile
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentAmplificationEligibility
local notation "O"=>ActualEisensteinCubic.O

attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationRadicalFamily.instDecidableEqSumFinOfNatNat_definitions
theorem exists_radical_row (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤ radicalBound η m p k ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (p^(2*k)) n:=by
  by_cases hk:k=0
  · obtain ⟨τ,hN,hτ⟩:=exists_supported_row_presentation η m 1 hm
      CenteredMomentAddedZero.supported_one_element hmLam hm2
    refine ⟨τ,?_,?_⟩
    · simp [radicalBound,hk,hN]
    · simpa [hk] using hτ
  · obtain ⟨τ,hM,hN,hτ⟩:=exists_radical_row_presentation η m hm hmLam hm2
      (fun _:Fin 1=>p) (fun _=>hs) (fun _=>2*k)
      (fun _=>Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hk))
    refine ⟨τ,?_,?_⟩
    · simpa [radicalBound,hk] using hN
    · simpa using hτ

theorem exists_radical_height (η:Character)(χ:RayCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤ radicalBound (childCharacter η χ) m p k ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom (p^(2*k)) I*
          rayCharacter χ (primaryGenerator I):=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_row (childCharacter η χ) m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he:=idealCoeff_eq_row (childCharacter η χ) τ m 1 (p^(2*k)) hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom (p^(2*k)) I*rayCharacter χ (primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem exists_radical_family (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hpp:goodLambda^2∣p-1)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p k) ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑χ:RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I:=by
  choose τ hN hτ using fun χ:RayCharacter=>exists_radical_height η χ m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn:=supported_primaryGenerator_ne_zero I hI
  have hgen:Supported (Ideal.span {primaryGenerator I}):=by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem exists_actual_error_family_oai (η:Character)(m p:O)
    (hm:m≠0)(hp:Prime p)(hs:Supported (Ideal.span {p}))
    (hpp:goodLambda^2∣p-1)(hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀(S:Finset (Ideal O))(C:Ideal O),C≠0→∀(β:Ideal O→ℂ)(t:ℝ)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I=>β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I=>residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑χ:RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I=>β (C*I)) (heightCoeff (τ χ) t) W K).re:=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_family η m p hm hs hpp hmLam hm2 (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact amplification_family_energy η m p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) C hC β t W K hK hW

end SevenEighths.CenteredMomentAmplificationRadicalFamily

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentAmplificationRadicalFamily.exists_actual_error_family_oai := @OAI.SevenEighths.CenteredMomentAmplificationRadicalFamily.exists_actual_error_family_oai
