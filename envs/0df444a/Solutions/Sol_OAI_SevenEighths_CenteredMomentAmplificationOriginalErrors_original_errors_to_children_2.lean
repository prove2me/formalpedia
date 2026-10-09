-- Prove2me | solution 2 for OAI.SevenEighths.CenteredMomentAmplificationOriginalErrors.original_errors_to_children
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:33:41.881119+00:00
-- url     : https://prove2.me/submissions/c8a241dd-c364-4e6b-9bfc-138f7f9a6926

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_CenteredMomentAmplificationErrorEnergy_finite_original_error_energy
import Theorems.Thm_OAI_SevenEighths_CenteredMomentAmplificationLiveEnergy_original_masked_child_energy

section
-- module Solutions.OAIHecke.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open Polynomial

/-- Backport (Mathlib d13f23b), with Mathlib's own proof. -/
theorem multiplicity_eq_zero_of_not_dvd {α : Type*} [Monoid α] {a b : α} (h : ¬ a ∣ b) :
    multiplicity a b = 0 :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_zero.mpr h)
end

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocation
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocation
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_power (I : Ideal O) (n : ℕ) :
    primaryGenerator (I ^n) = primaryGenerator I ^ n := map_pow primaryGeneratorHom I n

end SevenEighths.CenteredMomentAmplificationAllocation

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSectors
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

end SevenEighths.CenteredMomentCommonSectors

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LiveDomain
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentLiveDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

theorem source_gaussPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*primaryGaussRow I z := by
  unfold gaussPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*primaryGaussRow I z)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [primaryGaussRow,dif_pos (Finset.mem_filter.mp I.property).2]
  rfl

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentLiveDomain

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
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem residualIdeal_supported (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dif_pos hI]
  exact primeRemainder_supported p hp (primaryGenerator I)
    (by rw [primary_span_supported I hI];exact hI)

theorem residualIdeal_reconstruct (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    (Ideal.span {p})^(multiplicity p (primaryGenerator I))*residualIdeal p hp I=I := by
  rw [residualIdeal,dif_pos hI,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton,
    ← (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).1]
  exact primary_span_supported I hI

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePolynomial
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePolynomial
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

 theorem supported_residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    supportedColumns (residualColumns S p hp k)=residualColumns S p hp k := by
  apply Finset.filter_eq_self.mpr
  exact residualColumns_supported S p hp k

end SevenEighths.CenteredMomentAmplificationSourcePolynomial

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
open CenteredMomentAmplificationAllocation CenteredMomentAmplificationSourceDomain
open CenteredMomentSourceRow CenteredMomentLiveDomain CenteredMomentFirstSectors
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem residualIdeal_coprime (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    IsCoprime (Ideal.span {p}) (residualIdeal p hp I) := by
  rw [residualIdeal,dif_pos hI,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr
    (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).2

theorem residualColumns_eq (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2 ∣ p-1) (k : ℕ) :
    residualColumns S p hp k=
      (supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)).filter
        (fun I => IsCoprime (Ideal.span {p}) I) := by
  ext I
  constructor
  · intro hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    have hsJ := valuationColumns_supported S p k J hJ
    have hh := residualIdeal_reconstruct p hp J hsJ
    rw [(Finset.mem_filter.mp hJ).2] at hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,residualIdeal_supported p hp J hsJ⟩,
      residualIdeal_coprime p hp J hsJ⟩
    apply (mem_residualPool _ _ S _).mpr
    rw [hh]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
  · intro hI
    obtain ⟨hI,hcop⟩ := Finset.mem_filter.mp hI
    obtain ⟨hpool,hsI⟩ := Finset.mem_filter.mp hI
    have hIS := (mem_residualPool _ _ S I).mp hpool
    let J := (Ideal.span {p})^k*I
    have hsJ : Supported J := by
      rw [supported_mul_iff]
      constructor
      · simpa only [← Ideal.span_singleton_pow] using supported_power p hs k
      · exact hsI
    have hgen : primaryGenerator J=p^k*primaryGenerator I := by
      rw [show J=(Ideal.span {p})^k*I from rfl,primaryGenerator_mul,primaryGenerator_power,
        primaryGenerator_span p hp.ne_zero hpp]
    have hcop' : IsCoprime p (primaryGenerator I) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [primary_span_supported I hsI]
      exact hcop
    have hv : multiplicity p (primaryGenerator J)=k := by
      rw [hgen,multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
        (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_primaryGenerator_ne_zero I hsI))),
        multiplicity_pow_self_of_prime hp,
        multiplicity_eq_zero_of_not_dvd (hp.irreducible.coprime_iff_not_dvd.mp hcop'),add_zero]
    have hj : J∈valuationColumns S p k :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hIS,hsJ⟩,hv⟩
    refine Finset.mem_image.mpr ⟨J,hj,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero k hs.1)
    have hh := residualIdeal_reconstruct p hp J hsJ
    simpa only [hv] using hh

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

theorem exists_second_height_character (η : Character) (χ : RayCharacter) (m A : O)
    (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,τ.modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
          rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) m 1 A hm one_ne_zero hA hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he := idealCoeff_eq_row (childCharacter η χ) τ m 1 A hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom A I*rayCharacter χ (CompletedGauss.primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

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

theorem exists_amplification_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I := by
  choose τ hN hτ using fun χ : RayCharacter =>
    exists_second_height_character η χ m (p^(2*k)) hm (pow_ne_zero _ hp) hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn := supported_primaryGenerator_ne_zero I hI
  have hgen : Supported (Ideal.span {primaryGenerator I}) := by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

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

theorem exists_amplification_energy_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ (Q : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p k (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_family η m p hm hp hs hpp hmLam hm2 k
  exact ⟨τ,hN,fun Q C hC β t W K hK hW => amplification_family_energy η m p k τ hτ Q C hC β t W K hK hW⟩

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

theorem exists_actual_error_family (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1
        (p^(2*errorMovingExponent n))) ∧
      ∀ (S : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_energy_family η m p hm hp.ne_zero hs hpp hmLam hm2
    (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact hτ (residualColumns S p hp (n+1)) C hC β t W K hK hW

end SevenEighths.CenteredMomentAmplificationActiveFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSupport IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentCommonSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 local instance instDecidableEqSumFinOfNatNat_solutions_r848f37_1 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
theorem allocation_slot_one (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (i : ι) : B.val (Sum.inl i)=1 := by
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp (Finset.mem_filter.mp B.property).1
  have hi := Fintype.mem_piFinset.mp hv (Sum.inl i)
  have hd := hslot i (v (Sum.inl i)) hi
  have he := congrFun hvB (Sum.inl i)
  have hc : IsCoprime (P^k) (v (Sum.inl i)) := hd.2.pow_left
  have hh := supportExtract_of_disjoint (v (Sum.inl i)) (primeSupport (P^k))
    ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff (pow_ne_zero k hP) hd.1).mpr hc).symm
  exact he.symm.trans hh

 theorem allocation_plain_product (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : B.val (Sum.inr 0)*B.val (Sum.inr 1)=P^k := by
  have he := (Finset.mem_filter.mp B.property).2
  rw [Fintype.prod_sum_type,show (∏ i : ι,B.val (Sum.inl i))=1 by
    simp only [allocation_slot_one S P hP k hslot B,Finset.prod_const_one],one_mul,
    Fin.prod_univ_two] at he
  exact he

 theorem allocation_plain_injective (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    Function.Injective (fun B : actualAllocations S (P^k) => B.val (Sum.inr 0)) := by
  intro B D he
  have hb := allocation_plain_product S P hP k hslot B
  have hd := allocation_plain_product S P hP k hslot D
  have hb0 := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1 (Sum.inr 0)
  have he1 : B.val (Sum.inr 1)=D.val (Sum.inr 1) := by
    apply mul_left_cancel₀ hb0
    exact (hb.trans hd.symm).trans (congrArg (fun x => x*D.val (Sum.inr 1)) he.symm)
  apply Subtype.ext
  funext i
  cases i with
  | inl i => rw [allocation_slot_one S P hP k hslot B,allocation_slot_one S P hP k hslot D]
  | inr i => fin_cases i <;> assumption

 theorem idealDivisors_prime_power_card (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (idealDivisors (P^k)).card≤k+1 := by
  have hs : idealDivisors (P^k)⊆(Finset.range (k+1)).image (fun j => P^j) := by
    intro I hI
    obtain ⟨j,hj,he⟩ := (dvd_prime_pow hP k).mp ((mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mp hI)
    have heq : I=P^j := dvd_antisymm he.dvd he.symm.dvd
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),heq.symm⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (Finset.card_range (k+1)))

theorem actual_amplification_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤k+1 := by
  let f : actualAllocations S (P^k) → idealDivisors (P^k) := fun B =>
    ⟨B.val (Sum.inr 0),(mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mpr
      ⟨B.val (Sum.inr 1),(allocation_plain_product S P hP.ne_zero k hslot B).symm⟩⟩
  have hf : Function.Injective f := by
    intro B D he
    exact allocation_plain_injective S P hP.ne_zero k hslot (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hh
  exact hh.trans (idealDivisors_prime_power_card P hP k)

end SevenEighths.CenteredMomentAmplificationAllocationCost

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationScale
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem frozenCoefficient_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    frozenCoefficient B (P^k) R ν Wslot scale=(if IsCoprime (P^k) R then 1 else 0) := by
  unfold frozenCoefficient
  have he : Finset.univ.filter (fun i => B.val (Sum.inl i)≠1)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    exact not_not_intro (allocation_slot_one S P hP k hslot B i)
  rw [he,Finset.prod_empty,one_mul]

 theorem frozenCoefficient_norm_le (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    ‖frozenCoefficient B (P^k) R ν Wslot scale‖≤1 := by
  rw [frozenCoefficient_exact S P hP k hslot B R ν Wslot scale]
  split_ifs <;> simp

end SevenEighths.CenteredMomentAmplificationAllocationScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationChildEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationLiveEnergy CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationChildEnergy.instDecidableEqSumFinOfNatNat_definitions
theorem actual_amplification_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (Q R s : Ideal O) (hQ : Prime Q) (hQs : Supported Q) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime Q I)
    (hsc : IsCoprime s (Q^k))
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool (Q^k) (pow_ne_zero k hQ.ne_zero) (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime (Q^k) I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) ((Q^k)*I) else 0) f W K).re≤
      (k+1:ℝ)*∑ B : actualAllocations S (Q^k),
        (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  have hsPow : ∀ n : ℕ,Supported (Q^n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using CenteredMomentAddedZero.supported_one_ideal
    | succ n ih => rw [pow_succ,supported_mul_iff];exact ⟨ih,hQs⟩
  have hC := hsPow k
  have he := original_masked_child_energy S hS hp (Q^k) R s hC hsc ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K hK hW
  let E : actualAllocations S (Q^k) → ℝ := fun B =>
    (sourceGaussEnergy
      (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re
  have hE (B : actualAllocations S (Q^k)) : 0≤E B := sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hc : ((actualAllocations S (Q^k)).card:ℝ)≤(k+1:ℝ) := by
    exact_mod_cast actual_amplification_allocations_card S Q hQ k hslot
  have hf (B : actualAllocations S (Q^k)) :
      ‖frozenCoefficient B (Q^k) R ν Wslot P‖^2≤1 := by
    have hh := frozenCoefficient_norm_le S Q hQ.ne_zero k hslot B R ν Wslot P
    nlinarith [norm_nonneg (frozenCoefficient B (Q^k) R ν Wslot P)]
  exact he.trans (mul_le_mul (by exact hc)
    (Finset.sum_le_sum (fun B _ => mul_le_of_le_one_left (hE B) (hf B)))
    (Finset.sum_nonneg (fun B _ => mul_nonneg (sq_nonneg _) (hE B))) (by positivity))

end SevenEighths.CenteredMomentAmplificationChildEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationErrorPool
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorPool
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePolynomial
open CenteredMomentAmplificationSourcePool CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentGaussEnergy CenteredMomentFirstSectors CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem residual_polynomial_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (hk : 0<k) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
      (sourceGenerator_supported (residualColumns S p hp k))
      (fun I : supportedColumns (residualColumns S p hp k) => c ((Ideal.span {p})^k*I)*f I) h=
    gaussPolynomial Finset.univ
      (sourceGenerator (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (sourceGenerator_supported (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S))
      (fun I : supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S) =>
        (if IsCoprime ((Ideal.span {p})^k) (I:Ideal O) then c ((Ideal.span {p})^k*I) else 0)*f I) h := by
  let C := (Ideal.span {p})^k
  let Q := residualPool C (pow_ne_zero k hs.1) S
  refine (source_gaussPolynomial _ (fun I => c (C*I)*f I) h).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial Q
    (fun I => (if IsCoprime C I then c (C*I) else 0)*f I) h).symm
  rw [supported_residualColumns,residualColumns_eq S p hp hs hpp k,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [C]
  rw [IsCoprime.pow_left_iff hk]
  split_ifs <;> simp only [zero_mul]

 theorem residual_energy_eq_punctured (S : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (hk : 0<k) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp k) (fun I => c ((Ideal.span {p})^k*I)) f W K=
      sourceGaussEnergy (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)
        (fun I => if IsCoprime ((Ideal.span {p})^k) I then c ((Ideal.span {p})^k*I) else 0) f W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro h
  rw [residual_polynomial_eq_punctured S c f p hp hs hpp k hk h]

end SevenEighths.CenteredMomentAmplificationErrorPool

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem localErrorCost_nonneg (p : O) (n : ℕ) : 0≤localErrorCost p n := by
  unfold localErrorCost
  split_ifs <;> positivity

end SevenEighths.CenteredMomentAmplificationErrorEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AmplificationOriginalErrors
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationOriginalErrors
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentAmplificationSourceDomain CenteredMomentOriginalChildEnergy
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentAmplificationOriginalErrors.instDecidableEqSumFinOfNatNat_definitions
theorem original_errors_to_children_oai (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0<T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤_
    rw [hpool]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
        hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring

end SevenEighths.CenteredMomentAmplificationOriginalErrors

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentAmplificationOriginalErrors.original_errors_to_children_oai.{u_1} := @OAI.SevenEighths.CenteredMomentAmplificationOriginalErrors.original_errors_to_children_oai.{u_1}
