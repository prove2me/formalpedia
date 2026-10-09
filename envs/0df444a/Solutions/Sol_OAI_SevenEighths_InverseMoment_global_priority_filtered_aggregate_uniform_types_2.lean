-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.global_priority_filtered_aggregate_uniform_types
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:38:38.266417+00:00
-- url     : https://prove2.me/submissions/1a4d541d-99fc-4c98-9f71-ffd6fcd20805

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019
import Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_priority_source_moving_radius_window_order_uniform_types

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
theorem unitFourierCoeff_sum_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ‖unitFourierCoeff f χ‖) ≤ (Fintype.card Rˣ : ℝ) * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => unitFourierCoeff_norm_le f B hf χ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

theorem phaseCoeff_sum_norm_le (f : RayRing → ℂ) (B : ℝ)
    (hf : ∀ u : RayRingˣ, ‖f (u : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ‖phaseCoeff f χ‖) ≤ 16 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1)
  exact (unitFourierCoeff_sum_norm_le _ B hf).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast rayUnit_card_le) hB)

theorem fixedGQuotientValue_norm_le_two (r : RayRing) : ‖fixedGQuotientValue r‖ ≤ 2 := by
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ cubicTwoIdeal) ℂ :=
    (cubicChar cubicTwoIdeal cubicTwoIdeal_good).ringHomComp eisEmbedding
  let x := Ideal.Quotient.mk cubicTwoIdeal (lift (residueQuotientFour r))
  have hc : ‖(χ x)⁻¹‖ ≤ 1 := by
    simpa only [MulChar.inv_apply_eq_inv'] using norm_char_le_one (χ⁻¹) x
  change ‖(χ x)⁻¹ * quadraticRayValue (residueQuotientFour r)‖ ≤ 2
  rw [norm_mul]
  calc
    _ ≤ 1 * 2 := mul_le_mul hc (quadraticRayValue_bounds _).1 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

theorem gCoeff_sum_norm_le : (∑ χ : RayCharacter, ‖gCoeff χ‖) ≤ 32 := by
  exact (phaseCoeff_sum_norm_le _ 2 (fun u => fixedGQuotientValue_norm_le_two u)).trans_eq (by norm_num)

end RayFourExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
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

namespace FirstCauchyArithmetic

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

end FirstCauchyArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
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
namespace FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

end FirstPassCubeLabels

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.QuadraticProfiles
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

open scoped BigOperators Classical SchwartzMap FourierTransform

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic MixedCrossSeparation FirstCauchyArithmetic RayFourExpansion

theorem coreRayCoefficient_norm_le {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) :
    ‖coreRayCoefficient p F negative χ η ξ‖ ≤ ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
  have hη : ‖supportRay p η F‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one η _
  have hmul : ‖crossCoeff χ η‖ * ‖supportRay p η F‖ ≤ ‖crossCoeff χ η‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hη
  cases negative <;> simp only [coreRayCoefficient, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star]
  all_goals exact mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

theorem coreRayCoefficient_mass {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
      ‖coreRayCoefficient p F negative χ η ξ‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
      gcongr with χ _ η _ ξ _
      exact coreRayCoefficient_norm_le p F negative χ η ξ
    _ = (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ ξ : RayCharacter, ‖gCoeff ξ‖) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ 512 * 32 := mul_le_mul crossCoeff_sum_norm_le gCoeff_sum_norm_le (by positivity) (by norm_num)
    _ = 32 * 512 := by ring

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
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

open scoped BigOperators Classical
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

theorem secondRayCoefficient_mass :
    (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) ≤ 512 * 32 ^ 2 := by
  have hG := RayFourExpansion.gCoeff_sum_norm_le
  have hQ := RayFourExpansion.crossCoeff_sum_norm_le
  have heq : (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) =
      (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ a : RayCharacter, ‖gCoeff a‖) ^ 2 := by
    simp only [secondRayCoefficient, Fintype.sum_prod_type, norm_mul, norm_star, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro χ hχ
    apply Finset.sum_congr rfl
    intro η hη
    ring
  rw [heq]
  exact mul_le_mul hQ (pow_le_pow_left₀ (by positivity) hG 2) (by positivity) (by norm_num)

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer
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

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory

section
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient coreRayTwist dilatedCoreRow
  b0Label jLabel columnLog )
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)
open FourierBridge (logPhase)

lemma sideRayMonoid_norm_le_one (negative : Bool) (χ : RayCharacter) (a : O) :
    ‖sideRayMonoid negative χ a‖ ≤ 1 := by
  cases negative <;> simp only [sideRayMonoid, Bool.false_eq_true, ite_false, ite_true,
    conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  all_goals exact FiniteRayExpansion.norm_char_le_one _ _

lemma firstCoreTwist_norm_le (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) (a : O) :
    ‖firstCoreTwist negative χ Ψ r a‖ ≤ ‖Ψ a‖ := by
  have hc : ‖coreRayTwist negative r.1 r.2.2 a‖ ≤ 1 := by
    change ‖RayFourExpansion.rayCharacter (FirstPassCubeLabels.coreRayCharacter negative r.1 r.2.2) a‖ ≤ 1
    exact FiniteRayExpansion.norm_char_le_one _ _
  simp only [firstCoreTwist, MonoidHom.mul_apply, norm_mul]
  calc
    _ ≤ 1 * (‖Ψ a‖ * 1) := by gcongr; exact sideRayMonoid_norm_le_one _ _ _
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem firstCoreOuter_norm_le
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) :
    ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ ≤
      ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        ‖Ψ (∏ i ∈ D, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  have hc : ‖coreRayTwist negative r.1 r.2.2 (∏ i ∈ D, p i)‖ ≤ 1 := by
    change ‖RayFourExpansion.rayCharacter (FirstPassCubeLabels.coreRayCharacter negative r.1 r.2.2) (∏ i ∈ D, p i)‖ ≤ 1
    exact FiniteRayExpansion.norm_char_le_one _ _
  have hs : ‖(if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg D (-1))
      else 1 : ℂ)‖ ≤ 1 := by
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true, norm_one, norm_star]
    · exact le_rfl
    · exact finiteSquarefreeRow_norm_le_one _ hg D _
  simp only [firstCoreOuter, norm_mul, MonoidHom.mul_apply]
  calc
    _ ≤ ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        (‖Ψ (∏ i ∈ D, p i)‖ * 1) * 1 * 1 := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
theorem firstCoreOuter_mass
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    (∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ r : FirstCoreIndex,
        ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact (firstCoreOuter_norm_le p hg B v ε₁ ε₂ negative Ψ m D r).trans
        (mul_le_of_le_one_right (norm_nonneg _) hΨ)
    _ ≤ 32 * 512 := by
      simpa only [Fintype.sum_prod_type] using
        FirstPassCubeLabels.coreRayCoefficient_mass p (cubeOddSupport B v ε₁ ε₂) negative

end

open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient dilatedCoreRow b0Label jLabel
  columnLog )
open RayFourExpansion (RayCharacter crossCoeff)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label jLabel)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
namespace SecondPassIntegration
open JointLogSeparation FourierBridge

lemma logPhase_conjugate (t x : ℝ) : star (logPhase t x) = logPhase (-t) x := by
  unfold logPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring

end SecondPassIntegration

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open ActualEisensteinCubic

theorem mem_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (x : SecondExpansionData ι) :
    x ∈ secondExpansionPool F K ↔
      x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
        x.frequency ∈ K x.sourceCommon x.divisor := by
  simp only [secondExpansionPool, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨G,hG,E,hE,V,hV,k,hk,hx⟩
    subst x
    exact ⟨hG,hE,hV,hk⟩
  · rintro ⟨hG,hE,hV,hk⟩
    exact ⟨x.sourceCommon,hG,x.divisor,hE,x.overlap,hV,x.frequency,hk,rfl⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference
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

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_ge_one (S : Finset ι) : 1 ≤ primeProductNorm p S :=
  by
    rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {∏ i ∈ S, p i}) ≠ 0 by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondProfileIdentity
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem secondSourcePairKernel_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (G V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (e k : Eis) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondSourcePairKernel p e k
      (fun U => W₁ (primeProductNorm p G * primeProductNorm p U))
      (fun U => W₂ (primeProductNorm p G * primeProductNorm p U)) Φ Y (V ∪ N) (V ∪ M) =
    secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
      ![primeProductNorm p G, ‖eisEmbedding e‖^2, primeProductNorm p V,
        ‖eisEmbedding k‖^2, primeProductNorm p N, primeProductNorm p M] := by
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S, p i)‖ = Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hV : 0 ≤ primeProductNorm p V := (primeProductNorm_pos p hp V).le
  have hroots : Real.sqrt (primeProductNorm p V*primeProductNorm p N) *
      Real.sqrt (primeProductNorm p V*primeProductNorm p M) =
      primeProductNorm p V * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by
    rw [Real.sqrt_mul hV, Real.sqrt_mul hV]
    calc
      _ = (Real.sqrt (primeProductNorm p V))^2 * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  unfold secondSourcePairKernel secondNormProfile
  simp only [hs,primeProductNorm_union p V N hVN,primeProductNorm_union p V M hVM,
    Matrix.cons_val_zero,  Fin.isValue, Finset.prod_const_one, one_mul]
  have harg : Y * ‖eisEmbedding k‖^2 /
      (‖eisEmbedding e‖^2 * (primeProductNorm p V*primeProductNorm p N *
        (primeProductNorm p V*primeProductNorm p M))) =
      Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * (primeProductNorm p V)^2 *
        primeProductNorm p N * primeProductNorm p M) := by ring
  rw [harg]
  rw [← Complex.ofReal_mul, hroots]
  push_cast
  ring_nf

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondWholeKernel
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondSourcePairKernel_mark_factors {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (A₁ A₂ : Finset ι) (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (S T : Finset ι) :
    secondSourcePairKernel p e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*H₁ U)
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*H₂ U) W Y S T =
      star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)) * primeMark slots₂ lists₂ a₂ (A₂ ∪ T) *
        secondSourcePairKernel p e k H₁ H₂ W Y S T := by
  simp only [secondSourcePairKernel,star_mul]
  ring

theorem secondChildKernelPair_whole_profile {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F G V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂
      m r c d e k (-k)
      (secondSourcePairKernel p e k
        (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*W₁ (primeProductNorm p G*primeProductNorm p U))
        (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*W₂ (primeProductNorm p G*primeProductNorm p U)) Φ Y) =
    ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
      (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V,p i)
        (d*e*k) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V,p i)
          (d*e*(-k)) (fun _ => 1) M) *
      (star (primeMark slots₁ lists₁ a₁ (A₁ ∪ (V ∪ N))) *
        primeMark slots₂ lists₂ a₂ (A₂ ∪ (V ∪ M))) *
      secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
        ![primeProductNorm p G,‖eisEmbedding e‖^2,primeProductNorm p V,
          ‖eisEmbedding k‖^2,primeProductNorm p N,primeProductNorm p M] := by
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondSourcePairKernel_mark_factors]
  have hp := secondSourcePairKernel_profile p hp G V N M hVN hVM e k W₁ W₂ Φ Y
  rw [← hp]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualSecondProfile
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actualSecondProfileRow_eq_whole {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      ∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
            (secondActualNorms p x N M) :=
  secondChildKernelPair_whole_profile p hp hcop hg F x.common x.overlap x.extractedLeft x.extractedRight
    x.rayLeft x.rayRight x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ (fun z => W₁ (z/X)) (fun z => W₂ (z/X)) Φ Y

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Basic
namespace OAI

namespace SevenEighths.InverseMoment

theorem step_energy_exponent {F Fc kappa lambda count delta eta tau pi eps : ℝ}
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod] at he
  exact FirstCauchyArithmetic.family_product_injective _ hinj he

end SevenEighths.InverseInitialArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SlotAssignments
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem slotAssignmentWeight_norm_le_one (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) (q : ∀ i ∈ I, ι)
    (hq : q ∈ I.pi (fun i => L i ∩ A))
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) : ‖slotAssignmentWeight I a q‖ ≤ 1 := by
  rw [slotAssignmentWeight,norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  exact ha i.val i.property _ (Finset.mem_inter.mp (Finset.mem_pi.mp hq i.val i.property)).1

omit [DecidableEq σ] [DecidableEq ι] in
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

theorem pairedSlotWeight_norm_le_one (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))
    (hq : q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)))
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1) :
    ‖pairedSlotWeight J₁ J₂ a₁ a₂ q‖ ≤ 1 := by
  rw [pairedSlotWeight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (slotAssignmentWeight_norm_le_one J₁ L₁ a₁ A q.1 (Finset.mem_product.mp hq).1 ha₁)).trans
    (slotAssignmentWeight_norm_le_one J₂ L₂ a₂ A q.2 (Finset.mem_product.mp hq).2 ha₂)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
lemma indexedSlotAssignment_apply (I : Finset σ) (q : ∀ i ∈ I,ι) (i : σ) (hi : i ∈ I) :
    indexedSlotAssignment I q (I.equivFin ⟨i,hi⟩) = q i hi := by
  exact congrArg (fun j : I => q j.val j.property) ((I.equivFin).symm_apply_apply ⟨i,hi⟩)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem assignedSecondCoefficient_attach {Jo : ℕ}
    (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i ∈ J₁,ι) × (∀ i ∈ J₂,ι)) :
    assignedSecondCoefficient J₁ J₂ a₁ a₂ (attachPairedSlots J₁ J₂ (x,q)) =
      pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [assignedSecondCoefficient,attachPairedSlots,attachSecondSlots,
    pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem paired_assignment_filter (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (A : Finset ι) :
    ((J₁.pi L₁) ×ˢ (J₂.pi L₂)).filter (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ A) =
      (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hmem
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q.1 hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q.2 hq₂ k)).2

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem ActualSecondSourceConditions.mono {Jo Jn : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (h : ActualSecondSourceConditions p S)
    (hTS : T ⊆ S) : ActualSecondSourceConditions p T where
  admissible x hx := h.admissible x (hTS hx)
  common_disjoint x hx := h.common_disjoint x (hTS hx)
  first_divisor x hx := h.first_divisor x (hTS hx)
  second_divisor x hx := h.second_divisor x (hTS hx)
  old_support x hx := h.old_support x (hTS hx)
  new_support x hx := h.new_support x (hTS hx)
  quotient_nonzero x hx := h.quotient_nonzero x (hTS hx)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.PhysicalExponents
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

theorem second_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V δ A B j t g θ v η τ : ℝ) :
    Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
      (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z)) =
    Z^(secondLambda M r ell V δ A B j t g θ+18*η+τ) := by
  have he : Real.exp (6*(η*Real.log Z)) = Z^(6*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ,←Real.rpow_add hZ]
  congr 1
  unfold secondLambda secondFormalColumn
  ring

theorem physical_prefactor_identity (M r ell V δ A B R j t g θ v : ℝ) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j) = r+3*ell+V := by
  unfold firstKappa secondLambda firstPhysicalHeight secondCount secondFormalColumn secondFormalLabel
  ring

theorem physical_step_energy_exponent (M r ell V δ A B R j t g θ v η τ π ε clip : ℝ)
    (hclip : clip ≤ 6*η) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j+clip) +
      (9/2+18+11/2)*η+τ+π+ε ≤ r+3*ell+V+40*η+τ+π+ε :=
  step_energy_exponent (physical_prefactor_identity M r ell V δ A B R j t g θ v) hclip

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
theorem attachSecondExpansion_recover {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) :
    attachSecondExpansion (secondParentOf x) x.second = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondParentAssembly
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
theorem mem_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (x : MarkedSecondSource ι Jo 0) :
    x∈attachedSecondFamily parents source ↔
      secondParentOf x∈parents ∧ x.second∈source (secondParentOf x) := by
  simp only [attachedSecondFamily,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨parent,hp,y,hy,rfl⟩
    exact ⟨hp,hy⟩
  · rintro ⟨hp,hx⟩
    exact ⟨secondParentOf x,hp,x.second,hx,attachSecondExpansion_recover x⟩

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_family_conditions {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (ha : ∀ parent∈parents,parent.cube.Admissible)
    (hC : ∀ parent∈parents,Disjoint parent.firstCommon parent.cube.support)
    (hD : ∀ parent∈parents,parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ parent∈parents,∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : ∀ parent∈parents,parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (attachedSecondFamily parents source) := by
  have h (x : MarkedSecondSource ι Jo 0) (hx : x∈attachedSecondFamily parents source) :=
    (mem_attachedSecondFamily parents source x).mp hx
  constructor
  · intro x hx; exact ha (secondParentOf x) (h x hx).1
  · intro x hx; exact hC (secondParentOf x) (h x hx).1
  · intro x hx; exact hD (secondParentOf x) (h x hx).1
  · intro x hx; exact hE (secondParentOf x) (h x hx).1 x.second (h x hx).2
  · intro x hx i; exact hold (secondParentOf x) (h x hx).1 i
  · intro x hx i; exact Fin.elim0 i
  · intro x hx; exact hq (secondParentOf x) (h x hx).1

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.FirstPriorityParents
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem parent_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (parent p (Jo:=Jo)) := by
  intro x y h
  apply Source.ext
  · exact congrArg SecondParentSource.cube h
  · exact congrArg SecondParentSource.firstCommon h
  · exact congrArg SecondParentSource.firstDivisor h
  · exact sourceIdeal_injective p hinj (congrArg SecondParentSource.quotient h)
  · exact congrArg SecondParentSource.oldAssigned h

omit [DecidableEq ι] in
theorem appendParent_injective {Jn : ℕ} :
    Function.Injective (fun q : SecondParentSource ι Jo × (Fin Jn→SmoothMobiusCorrection.PrimeIdeal)=>
      appendParent q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [forget_append] using congrArg forgetAppended h
  · funext i
    simpa only [appendParent,Fin.addCases_right] using
      congrArg (fun x : SecondParentSource ι (Jo+Jn)=>x.oldAssigned (Fin.natAdd Jo i)) h

omit [DecidableEq σ] in
theorem attach_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) (J : Finset σ) :
    Function.Injective (attach p (Jo:=Jo) J) := by
  intro q r h
  have he := @appendParent_injective ι Jo (J.card+J.card)
    (parent p q.1,fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))
    (parent p r.1,fun i=>sourcePrime p (pairedSlotAssignment J J r.2 i)) h
  apply Prod.ext
  · exact parent_injective p hinj (congrArg Prod.fst he)
  · apply pairedSlotAssignment_injective J J
    funext i
    exact hinj (congrArg (fun q : SecondParentSource ι Jo ×
      (Fin (J.card+J.card)→SmoothMobiusCorrection.PrimeIdeal)=>(q.2 i).val) he)

omit [DecidableEq σ] in
theorem coefficient_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    coefficient p J a w (attach p J q)=w q.1*pairedSlotWeight J J a a q.2 :=
  (attach_injective p hinj J).extend_apply _ _ _

theorem extracted_prime_dvd (x : Source ι Jo) (hx : x.cube.Admissible)
    (negative : Bool) (i : ι) (hi : i∈extractedSupport negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · obtain hi|hi := Finset.mem_union.mp hi
    · have hb : i∈x.cube.support := by
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact hx.1 hi
        · exact hx.2 hi
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _) _
  · exact dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseFirstPriorityParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WholePriorityParents
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

lemma mem_wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈wholeAssignmentSource extra source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)) := by
  rw [←paired_assignment_filter]
  simp only [wholeAssignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈wholeAssignedParents p extra source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),attach p J (x,q)=y := by
  simp only [wholeAssignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.1,
      q,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_wholeAssignmentSource extra source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

theorem whole_extracted_prime_dvd (extra : Source ι Jo→Finset ι)
    (x : Source ι Jo) (hx : x.cube.Admissible) (he : extra x⊆x.cube.support)
    (negative : Bool) (i : ι) (hi : i∈wholeExtractedSupport extra negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i (he hi)) _) _
  · exact extracted_prime_dvd p x hx negative i hi

theorem whole_attach_old_support (extra : Source ι Jo→Finset ι)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x) (he : extra x⊆x.cube.support)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
      (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      whole_extracted_prime_dvd p extra x hx.admissible he negative _ (hh k)

theorem whole_assigned_family_conditions (hp : ∀ i,p i≠0)
    (extra : Source ι Jo→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (he : ∀ x∈source,extra x⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈wholeAssignedParents p extra source negative J lists,
      ∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p
      (attachedSecondFamily (wholeAssignedParents p extra source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact whole_attach_old_support p extra negative J lists x (hs x hx) (he x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

end SevenEighths.InverseMomentWholePriorityParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

theorem principalWindow_apply (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    principalWindow om a b ha hs negative t x =
      if negative then normTwistedSource (fun y => star (om y)) (-t) x
      else normTwistedSource om t x := by
  cases negative <;> simp only [principalWindow,Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,
    star_mul,logPhase_conjugate,mul_comm]

theorem principalWindow_norm (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    ‖principalWindow om a b ha hs negative t x‖=‖om x‖ := by
  rw [principalWindow_apply]
  cases negative <;> simp [normTwistedSource,logPhase_norm]

theorem principalWindow_support (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    Function.support (principalWindow om a b ha hs negative t) = Function.support om := by
  ext x
  change (_≠0) ↔ (_≠0)
  rw [←norm_ne_zero_iff,principalWindow_norm,norm_ne_zero_iff]

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.PrioritySecondSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InversePrioritySecondSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem quotientSupport_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (x : Source ι Jo) : quotientSupport p (parent p x)=x.quotientSupport :=
  (sourceIdeal_injective p hinj).extend_apply _ _ _

omit [DecidableEq σ] in
theorem quotientSupport_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    quotientSupport p (attach p J q)=q.1.quotientSupport :=
  quotientSupport_parent p hinj q.1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0) :
    x∈retainedPool p pool parents R label residual j ↔
      secondParentOf x∈parents ∧ x.second∈secondDyadicSector pool
        (secondVariableCutoff p (secondParentOf x) (R (secondParentOf x))) residual
        (label (secondParentOf x)) j := mem_attachedSecondFamily _ _ _

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InversePrioritySecondSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WholeRetainedSource
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMomentWholeRetainedSource
open ActualEisensteinCubic SecondPassArithmetic InverseMoment InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentWholePriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
      R label residual j) :
    ∀ i∈deleted p extra negative x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  have hy := ((mem_retainedPool p pool _ R label residual j x).mp hx).1
  obtain ⟨s,hs₀,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists _).mp hy
  have hc : x.cube=s.cube := (congrArg SecondParentSource.cube he).symm
  have hC : x.firstCommon=s.firstCommon := (congrArg SecondParentSource.firstCommon he).symm
  have ht : x.quotient=sourceIdeal p s.quotientSupport := (congrArg SecondParentSource.quotient he).symm
  have hqs : quotientSupport p (secondParentOf x)=s.quotientSupport := by
    rw [←he,quotientSupport_attach p hinj]
  intro i hi
  change i∈extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x)) at hi
  rw [hc,hC,hqs] at hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Or.inl (Finset.mem_union_left _ (hc.symm ▸ hextra s hs₀ hi))
  · rcases Finset.mem_union.mp hi with hi|hi
    · left
      rw [hc,hC]
      rcases Finset.mem_union.mp hi with hi|hi
      · apply Finset.mem_union_left
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact (hs s hs₀).admissible.1 hi
        · exact (hs s hs₀).admissible.2 hi
      · exact Finset.mem_union_right _ hi
    · right
      rw [ht]
      exact source_prime_dvd p _ i hi

theorem whole_coefficient_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈wholeAssignedParents p extra source negative J lists) :
    ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

end SevenEighths.InverseMomentWholeRetainedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.WholePriorityRetainedSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRetainedSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open InverseWholePriorityValidSource RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0) :
    x∈unifiedSource p pool parents R ↔ secondParentOf x∈parents ∧
      x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
      x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
        (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  rw [unifiedSource,mem_attachedSecondFamily,mem_secondExpansionPool]
  rfl

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem unified_mem_sector
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (x : MarkedSecondSource ι Jo 0) (hx : x∈unifiedSource p pool parents R) :
    x∈retainedPool p pool parents R label (x.second.sourceCommon\x.second.divisor)
      (label (secondParentOf x) (x.second.sourceCommon\x.second.divisor) x.second) := by
  obtain ⟨hy,hz⟩ := (mem_attachedSecondFamily _ _ x).mp hx
  apply (mem_retainedPool p _ _ _ _ _ _ x).mpr
  exact ⟨hy,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hz,rfl⟩,rfl⟩⟩

theorem unified_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (unifiedSource p pool
      (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists) R) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs he negative J lists
  intro y hy x hx
  exact ((mem_secondExpansionPool _ _ x).mp hx).2.1

theorem unified_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube)
      source negative J lists) R) :
    ∀ i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  exact InverseMomentWholeRetainedSource.retained_deleted_support p hinj extra source hs he
    negative J lists pool R (fun _ _ _=>()) _ () x
    (unified_mem_sector p pool _ R (fun _ _ _=>()) x hx)

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem deleted_lists (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (lists : σ→Finset ι) (x : MarkedSecondSource ι Jo 0) :
    residualLists p negative (fun i=>lists i\extra x.cube) (secondParentOf x)=
      fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x := by
  funext i
  ext k
  simp only [residualLists,InverseMomentWholeRetainedSource.deleted,Finset.mem_sdiff,Finset.mem_union]
  tauto

theorem wholeRow_eq (hp : ∀ i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a V X Y ray x =
      actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
        (slots\J) (slots\J)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        a a V V rowMajorant Y X := by
  unfold wholeRow retainedRow
  rw [deleted_lists]

theorem coefficientBound_pos : 0<coefficientBound := by norm_num [coefficientBound]

variable (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem priorityOuter_norm (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) (D : Finset ι)
    (hselector : ‖selector D‖≤1) (hΨ : ‖Ψ (∏ i∈D,p i)‖≤1) :
    ‖(priorityOuter p hg b negative Ψ m selector r core D:ℂ)‖≤ coefficientBound := by
  have hr : ‖crossCoeff r.1 r.2‖≤512 :=
    (Finset.single_le_sum (fun j _=>norm_nonneg (crossCoeff r.1 j)) (Finset.mem_univ r.2)).trans
      ((Finset.single_le_sum (fun j _=>Finset.sum_nonneg (fun k _=>norm_nonneg (crossCoeff j k)))
        (Finset.mem_univ r.1)).trans crossCoeff_sum_norm_le)
  have hc : ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖≤32*512 :=
    (Finset.single_le_sum (fun c _=>norm_nonneg (firstCoreOuter p hg b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D c))
      (Finset.mem_univ core)).trans
      (firstCoreOuter_mass p hg b.support _ b.leftBit b.rightBit negative Ψ m D hΨ)
  rw [Complex.norm_real,Real.norm_of_nonneg (by unfold priorityOuter; positivity)]
  unfold priorityOuter coefficientBound
  exact mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) hselector).trans hr) hc
    (norm_nonneg _) (by norm_num)

end SevenEighths.InverseWholePriorityRetainedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem globalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖globalPriorityWeight p hg negative Ψ m ray core w J a x‖≤ coefficientBound:=by
  apply InverseMomentWholeRetainedSource.whole_coefficient_norm p hinj (fun x=>extra x.cube)
    original negative J lists a _ coefficientBound ha
  · intro y hy
    rw [globalPriorityOuter,norm_mul]
    have hn:=priorityOuter_norm p hg y.cube negative Ψ m (fun _=>1) ray core y.quotientSupport
      (by simp) (hΨ _)
    exact (mul_le_mul (hw y hy) hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact ((mem_unifiedSource p pool _ R x).mp hx).1

theorem normalizedGlobalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x‖≤1:=by
  rw [normalizedGlobalPriorityWeight,norm_div,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  exact (div_le_one coefficientBound_pos).mpr
    (globalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hw hΨ J lists a ha R x hx)

omit [DecidableEq σ] in
theorem globalPriority_sum_normalized
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(J:Finset σ)(a:σ→ι→ℂ)
    (source:Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0))
    (H:MarkedSecondSource ι (Jo+(J.card+J.card)) 0→ℂ):
    (∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w J a x*H x)=
      (coefficientBound:ℂ)*∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x*H x:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold normalizedGlobalPriorityWeight
  have hn:(coefficientBound:ℂ)≠0:=by exact_mod_cast coefficientBound_pos.ne'
  field_simp
end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseSecondFibers InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem outerNorms_ge_one (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hk : x.second.frequency ≠ 0) :
    ∀ i,1 ≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact element_norm_ge_one _ hk

theorem frequency_ne_zero_of_gate (a : O) (R : ℝ) {k : O}
    (hk : k ∈ nonzeroChildFrequencyBall a R) : k ≠ 0 :=
  (Finset.mem_erase.mp hk).1

theorem dyadScale_pos (n : ℕ) : 0 < dyadScale n := by unfold dyadScale; positivity

theorem dyadIndex_bounds (r : ℝ) (hr : 1 ≤ r) :
    dyadScale (dyadIndex r) ≤ r ∧ r < 2*dyadScale (dyadIndex r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · have h := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hr0).mp (Nat.floor_le hlog)
    simpa only [dyadScale,dyadIndex,Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hr0).mp
      (Nat.lt_floor_add_one (Real.logb 2 r))
    have ht : r < (2:ℝ)^(dyadIndex r+1) := by
      rw [←Real.rpow_natCast]
      simpa only [Nat.cast_add,Nat.cast_one,dyadIndex] using h
    simpa only [dyadScale,pow_succ,mul_comm] using ht

omit [DecidableEq ι] in
theorem cell_subset (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : cell p source d ⊆ source := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem mem_keys_iff (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : d ∈ keys p source ↔ (cell p source d).Nonempty := by
  simp only [keys,Finset.mem_image,Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x,hx,he⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x,(mem_cell p source d x).mpr ⟨hx,he⟩⟩
  · intro h
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨x,(mem_cell p source d x).mp hx⟩

omit [DecidableEq ι] in
theorem cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (i : Fin 4) :
    1 ≤ outerNorms p x i / dyadScale (d i) ∧ outerNorms p x i / dyadScale (d i) < 2 := by
  obtain ⟨hxs,he⟩ := (mem_cell p source d x).mp hx
  have hb := dyadIndex_bounds _ (outerNorms_ge_one p hp x (hk x hxs) i)
  have hi : dyadIndex (outerNorms p x i) = d i := congrFun he i
  rw [hi] at hb
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hb.1),
    (div_lt_iff₀ (dyadScale_pos _)).mpr hb.2⟩

omit [DecidableEq ι] in
theorem keys_subset_capBox (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    keys p source ⊆ capBox A Z := by
  intro d hd
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (lt_of_lt_of_le zero_lt_one (outerNorms_ge_one p hp x (hk x hx) i)) (hcaps x hx i))

omit [DecidableEq ι] in
theorem keys_card_le_product (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    (keys p source).card ≤ ∏ i : Fin 4,(dyadIndex (Z^(A i))+1) := by
  have h := Finset.card_le_card (keys_subset_capBox p hp source hk A Z hcaps)
  simpa [capBox,Fintype.card_piFinset] using h

theorem capConstant_nonneg (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    0 ≤ capConstant A := by
  unfold capConstant
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hA i)) (Real.log_pos (by norm_num)).le

theorem cap_bin_bound (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) (Z : ℝ) (hZ : 2 ≤ Z)
    (i : Fin 4) : (dyadIndex (Z^(A i)) : ℝ)+1 ≤ 1+capConstant A*Real.log Z := by
  have hZ0 : 0 < Z := by linarith
  have hZi : 1 ≤ Z^(A i) := Real.one_le_rpow (by linarith) (hA i)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hZi)
  have hAi : A i ≤ ∑ j,A j := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  have hc := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAi
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le) (Real.log_nonneg (by linarith : 1 ≤ Z))
  dsimp [dyadIndex,capConstant]
  calc
    _ ≤ 1+Real.logb 2 (Z^(A i)) := by linarith
    _ = 1+(A i/Real.log 2)*Real.log Z := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hZ0,Real.logb]
      ring
    _ ≤ _ := by linarith

end SevenEighths.InverseSecondSourceBlocks

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

theorem second_cell_column_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := by
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

theorem second_cell_clipping_ratio (Z X b:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X)
    (hb:1≤b) (hsource:scales d 0*scales d 2≤b*X) :
    1≤Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d) ∧
    Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d)≤b := by
  let N:=secondCellColumnExponent Z X d
  have hz:0<Z:=lt_trans zero_lt_one hZ
  have hn:Z^N=X/(scales d 0*scales d 2):=second_cell_column_scale Z X d hZ hX
  constructor
  · exact Real.one_le_rpow hZ.le (sub_nonneg.mpr (le_max_right _ _))
  · by_cases hN:0≤N
    · rw [max_eq_right hN,sub_self,Real.rpow_zero];exact hb
    · have hN':N≤0:=le_of_not_ge hN
      rw [max_eq_left hN',zero_sub,Real.rpow_neg hz.le,hn,inv_div]
      exact (div_le_iff₀ hX).mpr hsource

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.PhysicalBlockBudget
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem second_source_scalar_norm (Y E V X : ℝ)
    (hY : 0<Y) (hE : 0<E) (hV : 0<V) (hX : 0<X) (a : ℂ) :
    ‖(Y:ℂ)*a*((E*V*X:ℝ):ℂ)⁻¹‖ = ‖a‖*(Y/(E*V*X)) := by
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,abs_of_pos (by positivity : 0<E*V*X)]
  ring

theorem physical_block_rpow_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
        (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z))) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hZpos : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_physical_scalar Z hZpos]
  have hexp : Real.exp ((9/2:ℝ)*(η*Real.log Z))=Z^((9/2:ℝ)*η) := by
    rw [Real.rpow_def_of_pos hZpos]
    congr 1
    ring
  rw [hexp,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hb := physical_step_energy_exponent M r ell V δ A B R j t g θ v η τ π ε
    (max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v) hclip
  nlinarith

theorem physical_block_scalar_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (ray : ℂ) (C : ℝ) (hC : 0≤C)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    C * Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Real.exp (6*(η*Real.log Z)) *
        ‖((Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ):ℝ):ℂ)*ray*
          ((Z^θ*Z^v*Z^(secondFormalColumn r A B t g v):ℝ):ℂ)⁻¹‖) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    C*‖ray‖*Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_source_scalar_norm _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (physical_block_rpow_budget Z hZ M r ell V δ A B R j t g θ v η τ π ε εmass hclip hεmass)
    (mul_nonneg hC (norm_nonneg ray))
  convert (preTransparency := .instances) hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem second_cell_scale_rpow (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    Z^(secondCellExponent Z d i)=scales d i :=
  Real.rpow_logb (by linarith) (ne_of_gt hZ) (dyadScale_pos _)

theorem second_cell_formal_column (Z r A B t:ℝ) (d:BlockIndex) (hZ:1<Z):
    secondCellColumnExponent Z (Z^(r-A-B-t)) d=
      secondFormalColumn r A B t (secondCellExponent Z d 0) (secondCellExponent Z d 2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  apply (Real.rpow_right_inj hz (ne_of_gt hZ)).mp
  rw [second_cell_column_scale Z _ d hZ (Real.rpow_pos_of_pos hz _)]
  rw [←second_cell_scale_rpow Z d 0 hZ,←second_cell_scale_rpow Z d 2 hZ,
    ←Real.rpow_add hz,←Real.rpow_sub hz]
  congr 1
  unfold secondFormalColumn
  ring

theorem second_cell_clipping_width (Z X b eta:ℝ) (d:BlockIndex)
    (hZ:1<Z) (hX:0<X) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*X) (hthreshold:b≤Z^(6*eta)) :
    max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d≤6*eta := by
  exact (Real.rpow_le_rpow_left_iff hZ).mp
    ((second_cell_clipping_ratio Z X b d hZ hX hb hsource).2.trans hthreshold)

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.PriorityCellBudget
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment
open InverseSecondSourceBlocks

theorem priority_cell_physical_budget
    (Z:ℝ) (hZ:1<Z) (d:BlockIndex)
    (M r ell V delta A B R j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ) (hC:0≤C) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*Z^(r-A-B-t))
    (hthreshold:b≤Z^(6*eta))
    (hmass:epsmass*(secondCount ell R j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) :
    let N:=secondCellColumnExponent Z (Z^(r-A-B-t)) d
    let Vchild:=secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta
    C*Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.exp (6*(eta*Real.log Z))*
        ‖((Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau):ℝ):ℂ)*ray*
          ((scales d 1*scales d 2*Z^N:ℝ):ℂ)⁻¹‖)*
      Z^((secondCount ell R j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
      Z^(2*(max 0 N+Vchild)+eps)≤
    C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  intro N Vchild
  have hz:0<Z:=zero_lt_one.trans hZ
  have hclip:=second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos hz _) hb hsource hthreshold
  rw [second_cell_formal_column Z r A B t d hZ] at hclip
  have he:=physical_block_scalar_budget Z hZ.le M r ell V delta A B R j t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) (secondCellExponent Z d 2)
    eta tau pi (eps+8*eta) epsmass ray C hC hclip hmass
  dsimp only [N,Vchild]
  rw [second_cell_formal_column Z r A B t d hZ]
  rw [second_cell_scale_rpow Z d 1 hZ,second_cell_scale_rpow Z d 2 hZ] at he
  convert (preTransparency := .instances) he using 1 <;> congr 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

theorem source_cell_joint_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (hk:∀x∈source,x.second.frequency≠0)
    (b X:ℝ) (hgeom:∀x∈source,primeProductNorm p x.second.sourceCommon*
      primeProductNorm p x.second.overlap≤b*X) (d:BlockIndex) (hd:d∈keys p source):
    scales d 0*scales d 2≤b*X := by
  obtain ⟨x,hx⟩:=(mem_keys_iff p source d).mp hd
  have h0:scales d 0≤primeProductNorm p x.second.sourceCommon:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).1
  have h2:scales d 2≤primeProductNorm p x.second.overlap:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 2).1
  exact (mul_le_mul h0 h2 (dyadScale_pos _).le (primeProductNorm_pos p hp _).le).trans
    (hgeom x (cell_subset p source d hx))

theorem priority_source_scalar_budget (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) :
    ∃ Cbin:ℝ,0≤Cbin ∧ ∀ {ι:Type*} [DecidableEq ι]
    (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ), 2≤Z → 0≤C → 1≤b → b≤Z^(6*eta) →
    (∀x∈source,x.second.frequency≠0) →
    (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
    (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t)) →
    (∀d∈keys p source,epsmass*(secondCount ell Ractive j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) →
    C*Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (∑d∈keys p source,priorityCellScalar Z (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
        (eta*Real.log Z) (Z^(r-A-B-t)) ell Ractive j t eta eps epsmass B ray d) ≤
    C*‖ray‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  refine ⟨capConstant caps,capConstant_nonneg caps hcaps,?_⟩
  intro ι _ p hp _ Jo Jn source Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
    ray hZ hC hb hthreshold hk hnorm hgeom hmass
  have hZ':1<Z:=lt_of_lt_of_le (by norm_num) hZ
  have hz:0<Z:=zero_lt_one.trans hZ'
  have hcard:((keys p source).card:ℝ)≤(1+capConstant caps*Real.log Z)^4:=by
    have h:=keys_card_le_product p hp source hk caps Z hnorm
    have hr:((keys p source).card:ℝ)≤∏i:Fin 4,((dyadIndex (Z^(caps i)):ℝ)+1):=by exact_mod_cast h
    apply hr.trans
    calc
      _≤∏_i:Fin 4,(1+capConstant caps*Real.log Z):=
        Finset.prod_le_prod (fun _ _=>by positivity) (fun i _=>cap_bin_bound caps hcaps Z hZ i)
      _= _:=by simp
  rw [Finset.mul_sum]
  calc
    _≤∑_d∈keys p source,C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps):=by
      apply Finset.sum_le_sum
      intro d hd
      have he:=priority_cell_physical_budget Z hZ' d M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
        ray hC hb (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold (hmass d hd)
      convert (preTransparency := .instances) he using 1 ; dsimp only [priorityCellScalar] ; ring
    _= ((keys p source).card:ℝ)*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=by simp
    _≤ (1+capConstant caps*Real.log Z)^4*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _= _:=by ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

lemma actual_profile_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X b : ℝ) (hX : 0<X)
    (hW : ∀y,W₁ y≠0 → y≤b)
    (hgeom : b*X<primeProductNorm p x.common*primeProductNorm p x.overlap) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X=0 := by
  rw [actualSecondProfileRow_eq_whole]
  apply Finset.sum_eq_zero
  intro N hN
  apply Finset.sum_eq_zero
  intro M hM
  have hzero : W₁ (primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N/X)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hX).mp (hW _ hn)
    have hlo := le_mul_of_one_le_right
      (mul_nonneg (primeProductNorm_pos p hp x.common).le (primeProductNorm_pos p hp x.overlap).le)
      (primeProductNorm_ge_one p hp N)
    linarith
  simp [secondNormProfile,secondActualNorms,hzero]

lemma wholeRow_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X Y b : ℝ) (hX : 0<X) (hW : ∀y,W y≠0 → y≤b)
    (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0)
    (hgeom : b*X<primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x=0 := by
  rw [wholeRow_eq]
  have hh := actual_profile_zero_of_geometry p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
    (slots\J) (slots\J) (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
    (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a W W rowMajorant Y X b hX hW hgeom
  rw [hh,mul_zero]

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_subset {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    geometrySource p source b X⊆source := Finset.filter_subset _ _

lemma original_retained_geometry_sum
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (MarkedSecondSource ι Jo 0)) (w : MarkedSecondSource ι Jo 0→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X Y b : ℝ)
    (hX : 0<X) (hW : ∀y,W y≠0 → y≤b) (ray : SecondRayIndex) :
    (∑x∈source,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x)=
    ∑x∈geometrySource p source b X,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x := by
  rw [geometrySource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs with hg₀
  · rfl
  · rw [wholeRow_zero_of_geometry p hp hcop hg extra pool negative Ψ m slots J lists a W X Y b hX hW
      ray x (lt_of_not_ge hg₀),mul_zero]

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.PriorityRetainedMovingRadiusWindowOrderUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_retained_moving_radius_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_source_moving_radius_window_order_uniform_types  om Φ lo hi hlo hsupport negative B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert (preTransparency := .instances) hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredEnergyUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_moving_radius_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_retained_moving_radius_window_order_uniform_types  om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsub:source⊆originalSource:=InverseMomentGlobalRetainedGates.geometrySource_subset p originalSource b X
  have hsource:ActualSecondSourceConditions p source:=
    ActualSecondSourceConditions.mono p (unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff) hsub
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    fun x hx=>unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff x (hsub hx)
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x (hsub hx)
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  have hupper:∀y,principalWindow om lo hi hlo hsupport negative t y≠0 → y≤b:=by
    intro y hy
    have hy':y∈Function.support om:=by
      rw [←principalWindow_support om lo hi hlo hsupport negative t]
      exact hy
    exact (hsupport hy').2.trans hhib
  rw [InverseMomentGlobalRetainedGates.original_retained_geometry_sum p hp hcop hg extra pool originalSource
    (globalPriorityWeight p hg negative Ψ m ray core w assigned a) negative Ψ₀ m slots assigned lists a
    (principalWindow om lo hi hlo hsupport negative t) X Y b hX hupper z]
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert (preTransparency := .instances) mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredRaysUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_all_rays_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_moving_radius_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert (preTransparency := .instances) h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤C*A*H*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
    _= _:=by dsimp [H];ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredAggregateUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_aggregate_uniform_types_oai
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w
          negative Ψ m slots lists a (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_all_rays_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  let Ctot:=(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:=C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
    P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤H:=by
    obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
      ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
    exact he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a (fun _=>cutoff)
      Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hZ:1<Z:=(hdata 1 1 ∅ (Finset.empty_subset _)).2.2.2.1
  have hH:0≤H:=by dsimp [H];positivity
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
  change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤H at hb
  change P*((32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤_
  calc
    _=(32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hr
      apply Finset.sum_congr rfl
      intro core hc
      apply Finset.sum_congr rfl
      intro assigned ha
      ring
    _≤(32*512)*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ray _=>Finset.sum_le_sum fun core _=>Finset.sum_le_sum fun assigned ha=>hb ray core assigned (Finset.mem_powerset.mp ha)
    _=(32*512)*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
      ring
    _≤(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
    _= _:=by dsimp [Ctot,H];ring
end SevenEighths.InverseMoment

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.global_priority_filtered_aggregate_uniform_types_oai := @OAI.SevenEighths.InverseMoment.global_priority_filtered_aggregate_uniform_types_oai
