-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.actual_marked_bin_height
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:12:59.887736+00:00
-- url     : https://prove2.me/submissions/1962371b-0451-454f-8213-7bdb5dcf5f54

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_long_bin_normalized_energy
import Theorems.Thm_OAI_SevenEighths_InverseMoment_original_two_pass_energy

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
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

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

end FiniteGaussPhase

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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

namespace CompletedGauss

section

open ActualEisensteinCubic

open ActualEisensteinCubic

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

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

end FirstPassCubeLabels

open scoped BigOperators Classical

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

section
open FourierBridge FirstPassCubeLabels

lemma source_le_profileSourceBound (g : 𝓢(ℝ, ℂ)) (J i : ℕ) (hi : i ≤ J) :
    (SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g ≤
      profileSourceBound g J := by
  unfold profileSourceBound
  apply Finset.single_le_sum (s := Finset.range (J + 1)) (a := i)
    (f := fun k : ℕ => (SchwartzMap.seminorm ℝ 0 k) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower k) g)
  · intro j hj
    positivity
  · exact Finset.mem_range.mpr (by omega)

end

open FirstPassCubeLabels

end JointLogSeparation

open scoped BigOperators

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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

lemma twistSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (K : ℕ) : 0 ≤ twistSourceBound g K := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))

theorem profileSourceBound_frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) (K : ℕ) :
    profileSourceBound (frequencyTwist g t) K ≤ twistSourceBound g K * (1 + ‖t‖)^K := by
  unfold profileSourceBound twistSourceBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ K := Finset.mem_range_succ_iff.mp hi
  have hb := add_le_add (frequencyTwist_seminorm_polynomial g t 0 i)
    (frequencyTwist_seminorm_polynomial g t (volume : Measure ℝ).integrablePower i)
  have hn : 0 ≤ (2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))
  calc
    _ ≤ ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
        (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i)) *
          (1 + ‖t‖)^i := by convert (preTransparency := .instances) hb using 1 ; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hin) hn

end JointLogSeparation

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FundamentalDomain
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

theorem largeCubeCoefficient_norm_le (H₀ : ℝ) (B : Ideal O) :
    ‖largeCubeCoefficient H₀ B‖ ≤ (idealDivisors B).card := by
  by_cases hB : B=⊥
  · simp [hB,largeCubeCoefficient]
  · rw [largeCubeCoefficient,if_neg hB]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ H∈idealDivisors B,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
        · simp only [if_pos h]
          by_cases hsf : Squarefree H
          · simp [hsf.moebius_eq]
          · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsf]
        · simp [h]
      _ = _ := by simp

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.GlobalScales
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

namespace CompletedGauss
open ActualEisensteinCubic

theorem largeCubeCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (H₀ : ℝ) (B : Ideal O),B≠⊥ →
      ‖largeCubeCoefficient H₀ B‖ ≤ C*(Ideal.absNorm B : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  exact ⟨C,hC,fun H₀ B hB => (largeCubeCoefficient_norm_le H₀ B).trans (hbound B hB)⟩

end CompletedGauss

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ReopeningSeparation
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace CanonicalCubeSeparation
open FourierBridge JointLogSeparation FirstPassCubeLabels

lemma cubeFrequencyFactor_bound (t ξ : ℝ) (ht : t ≤ 1) :
    ‖cubeFrequencyFactor t ξ‖ ≤ Real.exp (1/2) := by
  rw [cubeFrequencyFactor_norm]
  exact Real.exp_le_exp.mpr (by linarith)

end CanonicalCubeSeparation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss (actualSextic)

theorem rowTwist_norm (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (m f z n : ActualEisensteinCubic.O) :
    ‖rowTwist Ψ m f z n‖≤1 := by
  change ‖Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n})‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (idealRowHom_norm _ _)

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open SecondPassArithmetic hiding O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation
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

namespace CanonicalCubeSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation

lemma cube_log_bin (B n : ℝ) (hB : 0 < B) (hn : B ≤ n)
    (hn' : n ≤ Real.exp 1 * B) : Real.log (n/B) ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hn))
  · have hh : n/B ≤ Real.exp 1 := (div_le_iff₀ hB).mpr hn'
    have := Real.log_le_log (div_pos hn0 hB) hh
    simpa only [Real.log_exp] using this

lemma separatedCubeCoefficient_bound {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ Γ : ℝ) (hB : 0 < B) (hΓ : 0 ≤ Γ) (v : κ)
    (hn : B ≤ n v) (hn' : n v ≤ Real.exp 1*B) (hβ : ‖β v‖ ≤ Γ) :
    ‖separatedCubeCoefficient β n B ξ v‖ ≤ Γ*Real.exp (1/2) := by
  unfold separatedCubeCoefficient
  rw [norm_mul]
  exact mul_le_mul hβ (cubeFrequencyFactor_bound _ ξ (cube_log_bin B _ hB hn hn').2)
    (norm_nonneg _) hΓ

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace CanonicalRowCompletion

open ActualEisensteinCubic
open CompletedGauss hiding O

theorem cubeWeight_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ B‖ ≤ 1/(Ideal.absNorm B:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator B)‖ ≤ 1 := by
    by_cases hz : primaryGenerator B=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator B))^3*
    Ψ (primaryGenerator B)^3/(Ideal.absNorm B:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) hang)).trans (pow_le_one₀ (norm_nonneg _) (hΨ _))

theorem cubePhase_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubePhase Ψ B‖ ≤ 1 := by
  by_cases hB : B=0
  · simp [hB,cubePhase]
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  rw [cubePhase,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm B:ℝ)*(1/(Ideal.absNorm B:ℝ)) :=
      mul_le_mul_of_nonneg_left (cubeWeight_norm_le Ψ hΨ B) hN.le
    _ = 1 := by field_simp

theorem reopenedCubeCoefficient_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀(H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ), (∀z,‖Ψ z‖≤1) →
      ∀B:Ideal ActualEisensteinCubic.O,B≠0 → ‖reopenedCubeCoefficient H₀ Ψ B‖ ≤ C*(Ideal.absNorm B:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := largeCubeCoefficient_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro H₀ Ψ hΨ B hB
  rw [reopenedCubeCoefficient,norm_mul]
  calc
    _ ≤ ‖largeCubeCoefficient H₀ B‖*1 :=
      mul_le_mul_of_nonneg_left (cubePhase_norm_le Ψ hΨ B) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hbound H₀ B hB

end CanonicalRowCompletion

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RadialProfiles
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

namespace SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter

theorem radialFromLog_support (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : radialFromLog V hVs A hV x≠0) :
    Real.exp (-A)≤x ∧ x≤Real.exp A := positiveRadialProfile_support V A hV x hx

theorem radialFromLog_column {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (X : ℝ) (hX : 0<X) (S : Finset ι) :
    radialFromLog V hVs A hV (FirstPassCubeLabels.primeProductNorm p S/X)=
      V (FirstPassCubeLabels.columnLog p X S) :=
  radialFromLog_apply_pos V hVs A hV _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) hX)

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening
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
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem cubeIdeal_eq_primeProduct_span (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    Ideal.span {primeProduct (poolPrimary F) v.support v}=cubeIdeal F v := by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  simp only [←Ideal.span_singleton_pow,poolPrimary_span F hF]
  unfold cubeIdeal
  apply Finset.prod_subset (Finset.subset_univ v.support)
  intro i hi hni
  rw [Finsupp.notMem_support_iff.mp hni,pow_zero]

theorem cubeIdeal_primeProduct_norm (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2=
      (Ideal.absNorm (cubeIdeal F v):ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,cubeIdeal_eq_primeProduct_span F hF]

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

end CanonicalRowCompletion

open scoped BigOperators Classical

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DescentHeight
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
noncomputable section

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongSource
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCubeSeparation CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation FourierBridge CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

theorem long_frequency_profile
    {ι:Type*}(p:ι→O)(hp:∀i,p i≠0)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)
    (Z r ξ:ℝ)(hZ:0<Z)(T:Finset ι) :
    frequencyTwist V ξ (columnLog p (Z^r) T)=
      normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
        (primeProductNorm p T/Z^r) := by
  rw [normTwistedSource,radialFromLog_column p hp V (V.smooth ⊤) A hV _ (Real.rpow_pos_of_pos hZ r)]
  simp only [frequencyTwist_apply,columnLog]

theorem long_marked_source_eq
    {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(β:(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m f z:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)(Z r ξ:ℝ)(hZ:0<Z) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (T∪v.support)*
        frequencyTwist V ξ (columnLog p (Z^r) T)) z =
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (v.support∪T)*
        normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
          (primeProductNorm p T/Z^r)) z := by
  congr 1
  funext v T
  rw [long_frequency_profile p hp V A hV Z r ξ hZ T,Finset.union_comm T v.support]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongCoefficient
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem actualLongCoefficient_uniform (eps:ℝ)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}(p:ι→O)(_hp:∀i,p i≠0)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)
      (m:O)(H₀ B ξ:ℝ)(I:Ideal O)(v:ι→₀ℕ),0<B→
      B≤‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2→
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B→
      ‖actualLongCoefficient p Ψ m H₀ B ξ I v‖≤C*(Real.exp 1*B)^eps := by
  obtain ⟨C,hC,hbound⟩:=reopenedCubeCoefficient_small_power eps heps
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro ι p hp Ψ hΨ m H₀ B ξ I v hB hlo hhi
  have hne:Ideal.span {primeProduct p v.support v}≠0 := by
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i hi=>pow_ne_zero _ (hp i))
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hlo hhi
  have hh:=hbound H₀ (rowTwist Ψ m (idealGenerator I) 1)
    (rowTwist_norm Ψ hΨ m (idealGenerator I) 1) _ hne
  have hb:‖reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p v.support v})‖≤C*(Real.exp 1*B)^eps :=
    hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhi heps.le) hC.le)
  have hs:=separatedCubeCoefficient_bound
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ
    (C*(Real.exp 1*B)^eps) hB (by positivity) v hlo hhi hb
  unfold actualLongCoefficient
  convert (preTransparency := .instances) hs using 1 ; ring

theorem actualLongCoefficient_complete
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)(I:Ideal O)
    (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    actualLongCoefficient (poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D))
      Ψ (m*excludedGenerator S) H₀ B ξ I v=
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1)
        (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u):ℝ)) B ξ v := by
  simp only [actualLongCoefficient,cubeIdeal_eq_primeProduct_span _
    (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.TwoPassScalar
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment

theorem two_pass_scalar (C Cz Ct Γ A Z F M r ell eta tau _pi epsFirst loss Lcap saving lossFinal H:ℝ)
    (hC:0≤C)(hCz:0≤Cz)(hCt:0≤Ct)(hA:0≤A)(hZ:1≤Z)(hH:1≤H)
    (hM:M-ell≤F)
    (hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
    (hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
    (htail: -saving≤F+lossFinal):
    Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
      C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ct*Γ^2*Z^(-saving)≤
    (C+Cz+Ct)*Γ^2*(1+A)*H*Z^(F+lossFinal) :=by
  have hz:0<Z:=lt_of_lt_of_le zero_lt_one hZ
  have hP:=Real.rpow_le_rpow_of_exponent_le hZ (show M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta)≤F+lossFinal by linarith)
  have hT:=Real.rpow_le_rpow_of_exponent_le hZ htail
  have hR:=Real.rpow_le_rpow_of_exponent_le hZ (show F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤F+lossFinal by linarith)
  have hlarge:1≤(1+A)*H:=one_le_mul_of_one_le_of_one_le (by linarith) hH
  have hp:Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))≤Cz*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hP (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤Cz*Γ^2 by positivity)
  have ht:Ct*Γ^2*Z^(-saving)≤Ct*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hT (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤Ct*Γ^2 by positivity)
  have hr:C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤
      C*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    calc
      _=C*Γ^2*((1+A)*H)*Z^(F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)):=by simp only [Real.rpow_add hz];ring
      _≤_:=mul_le_mul_of_nonneg_left hR (by positivity)
  nlinarith [add_le_add (add_le_add hp hr) ht]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstTwoPassParentEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_two_pass_parent_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ b≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst→0<epsSecond→∀degree:ℕ,
      ∃C:ℝ,0≤C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta pi epschild A loss lossFinal:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Lcap)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤ r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hVcap:V≤Lcap)(_hwin:Real.exp window≤Z^eta)(_hpi:0≤pi)(_hpieta:6*eta≤pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤pi/4)
      (_hechild:0≤epschild)(_hsave: -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤loss)(_hcard:slots.card≤K)
      (_hparent:M-ell≤ r+3*ell+V)
      (_hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
      (_hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
      (_htail: -saving≤ r+3*ell+V+lossFinal)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hA:0≤A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*Γ^2*(1+A)*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) :=by
  obtain ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,he⟩:=
    original_two_pass_energy om a b ha hs Lcap eta tau saving em ed hcap hb heta heta1 htau htau1 hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨C,Cz,Ct,hC,hCz,hCt,he⟩:=he epsFirst epsSecond hepsF hepsS degree
  refine ⟨C+Cz+Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss lossFinal hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hΓ hA hsf hn hβ hlabels hslots hweights mark Y cutoff W source keys hl hr'
  have hall:=he p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hΨ hΓ hA hsf hn hβ hlabels hslots hweights hl hr'
  exact hall.trans (two_pass_scalar C Cz Ct Γ A Z (r+3*ell+V) M r ell eta tau pi epsFirst loss Lcap saving lossFinal
    ((1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))) hC hCz hCt hA (by linarith)
    (one_le_pow₀ (by linarith [norm_nonneg theta])) hparent hprincipal hretained htail)

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongParent
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_long_parent_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ b≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst→0<epsSecond→∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (Ψ:O→*ℂ)(m mCoef:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V H₀ ξ pi epschild A loss lossFinal:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hbinExp:Real.exp 1≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Lcap)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤ r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQlo:∀v∈Q,Z^ell≤‖eisEmbedding (primeProduct p v.support v)‖^2)
      (_hQhi:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*Z^ell)
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hVcap:V≤Lcap)(_hwin:Real.exp window≤Z^eta)(_hpi:0≤pi)(_hpieta:6*eta≤pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤pi/4)
      (_hechild:0≤epschild)(_hsave: -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤loss)(_hcard:slots.card≤K)
      (_hparent:M-ell≤ r+3*ell+V)
      (_hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
      (_hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
      (_htail: -saving≤ r+3*ell+V+lossFinal)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hA:0≤A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om ξ (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q ((actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*(1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) := by
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    original_two_pass_parent_energy om a b ha hs Lcap eta tau saving em ed hcap hb heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,hCcoef,hcoef⟩:=actualLongCoefficient_uniform epsFirst hepsF
  obtain ⟨C,hC,hfull⟩:=he epsFirst epsSecond hepsF hepsS degree
  refine ⟨Ccoef,C,hCcoef,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ pi epschild A loss lossFinal hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  have hβ:∀I∈labels,∀v∈Q,
      ‖actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ I v‖≤Ccoef*(Real.exp 1*Z^ell)^epsFirst := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  exact hfull p hp hg hinj hcop hc hpr pool Q labels
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) Ψ m slots lists weights
    Z M r ell V (Ccoef*(Real.exp 1*Z^ell)^epsFirst) ξ pi epschild A loss lossFinal hZ hbin hM hF hMcap hell hV hr hbZ
    hQpool hQ hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ (by positivity) hA hsf hn hβ hlabels hslots hweights hleft hright

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongUniformTestBin
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_bin_uniform_test
    (a₀ b₀:ℝ)(ha₀:0<a₀)(hb₀:0≤b₀)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀(test:ℝ → ℂ)(hs₀:Function.support test⊆Set.Icc a₀ b₀)(hTest:ContDiff ℝ ∞ test),
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 0≤M → r+3*ell+V≤Lcap → M≤Lcap →
        0≤ell → 0≤V → -eta≤ r → Real.exp Alog≤Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤Real.exp 1*Z^ell) →
        r≤Lcap → ell≤Lcap → V≤Lcap → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
        em*(20*(3*Lcap+16)+30)≤pi/4 → ed*(20*(3*Lcap+16)+30)≤pi/4 →
        0≤epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤loss → slots.card≤K →
        M-ell≤ r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤ r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z
          test (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^(InverseClippingProfiles.momentOrder (firstDegree degree)))^2 := by
  let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox
  have hs:Function.support om⊆Set.Icc (Real.exp (-Alog)) (Real.exp Alog):=
    fun x hx=>radialFromLog_support Vlog (Vlog.smooth ⊤) Alog hbox x hx
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    actual_long_parent_energy om (Real.exp (-Alog)) (Real.exp Alog) (Real.exp_pos _) hs
      Lcap eta tau saving em ed hcap (Real.exp_pos _).le heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,C,hCcoef,hC,hparent⟩:=he epsFirst epsSecond hepsF hepsS degree
  let d:=InverseClippingProfiles.momentOrder (firstDegree degree)
  refine ⟨Ccoef,C,hCcoef,hC,?_⟩
  intro test hs₀ hTest
  let moment:ℝ:=∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^d
  intro σ _ S D hbad hSp
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  intro Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hz:0<Z:=by linarith
  have hg' : ∀i:primePool F,goodLambda∉Ideal.span {poolPrimary F i}:=poolPrimary_good F hF
  have hinj:Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j hij
    exact Subtype.ext (by simpa only [poolPrimary_span F hF] using hij)
  have hpr (i:primePool F):goodLambda^2∣poolPrimary F i-1:=
    (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2
  let Gamma:=Ccoef*(Real.exp 1*Z^ell)^epsFirst
  let E:=C*Gamma^2*(1+A)*Z^(r+3*ell+V+lossFinal)
  have hE:0≤E:=by dsimp [E];positivity
  refine (actual_long_bin_normalized_energy S D hbad hSp Q labels Ψ m test a₀ b₀ ha₀ hb₀ hs₀ hTest
    Vlog hone Z r ell V H₀ (Z^M) E d hz hD (Real.rpow_pos_of_pos hz _) hE hQlo hQhi slots lists weights ?_).trans_eq ?_
  · intro ξ
    have hbnd:=hparent (poolPrimary F) (poolPrimary_ne_zero F hF) hg' hinj
      (poolPrimary_coprime F hF) (poolPrimary_odd F hF) hpr Finset.univ Q labels Ψ m (m*excludedGenerator S)
      slots lists weights Z M r ell V H₀ ξ pi epschild A loss lossFinal
      hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ (fun _ _=>Finset.subset_univ _)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQlo v hv)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQhi v hv)
      hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
      hΨ hA hsf hn hlabels hslots hweights (hleft ξ) (hright ξ)
    have hc (I:Ideal O) := funext (actualLongCoefficient_complete S D hbad Ψ m H₀ (Z^ell) ξ I)
    have hrow: (fun I z=>varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist Vlog ξ (columnLog (poolPrimary F) (Z^r) T)) z)=
      (fun I z=>varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ (primeProductNorm (poolPrimary F) T/Z^r)) z) := by
      funext I z
      exact long_marked_source_eq (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        hg' Finset.univ Q _ Ψ m (idealGenerator I) z slots lists weights Vlog Alog hbox Z r ξ hz
    rw [hrow]
    convert (preTransparency := .instances) hbnd using 1
    · apply congrArg (fun f => Z^(-r-2*ell-V)*rowFamilyEnergy labels f (Z^M))
      funext I z
      exact congrArg (fun coeff => varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q coeff Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ
          (primeProductNorm (poolPrimary F) T/Z^r)) z) (hc I).symm
    · dsimp [E,Gamma,d]
      try simp only [Real.norm_eq_abs]
      ring
  · dsimp [E,Gamma,moment]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalReopeningHeight
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseMoment
open MeasureTheory CanonicalCubeSeparation FourierBridge JointLogSeparation CompletedHeight

theorem reopening_coefficient_twist (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(theta:ℝ)
    (hT:ContDiff ℝ ∞ (normTwistedSource W theta)):
    reopeningCoefficient (normTwistedSource W theta) a b ha
      ((normTwistedSource_support W theta).trans hs) hT=
      𝓕 (frequencyTwist (sourceLogProfile W a b ha hs hW) theta) :=by
  unfold reopeningCoefficient
  congr 1
  ext x
  simp only [sourceLogProfile_apply,frequencyTwist_apply,normTwistedSource,Real.log_exp]

theorem reopening_twisted_moment (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)≤
      C*(1+‖theta‖)^(J+(volume:Measure ℝ).integrablePower) :=by
  obtain ⟨C,hC,he⟩:=frequencyTwist_fourier_moment J (sourceLogProfile W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro theta hT
  rw [reopening_coefficient_twist W a b ha hs hW theta hT]
  simpa only [Real.norm_eq_abs,mul_comm] using he theta

theorem reopening_twisted_moment_squared (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)^2≤
      C*(1+‖theta‖)^(2*(J+(volume:Measure ℝ).integrablePower)) :=by
  obtain ⟨C,hC,he⟩:=reopening_twisted_moment W a b ha hs hW J
  refine ⟨C ^2,sq_nonneg _,?_⟩
  intro theta hT
  have hh:=pow_le_pow_left₀ (integral_nonneg (fun ξ=>by positivity)) (he theta hT) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm] using hh

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongHeightBin
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_bin_height_oai
    (a₀ b₀:ℝ)(ha₀:0<a₀)(hb₀:0≤b₀)
    (W:ℝ→ℂ)(hsW:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀theta:ℝ,
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 0≤M → r+3*ell+V≤Lcap → M≤Lcap →
        0≤ell → 0≤V → -eta≤ r → Real.exp Alog≤Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤Real.exp 1*Z^ell) →
        r≤Lcap → ell≤Lcap → V≤Lcap → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
        em*(20*(3*Lcap+16)+30)≤pi/4 → ed*(20*(3*Lcap+16)+30)≤pi/4 →
        0≤epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤loss → slots.card≤K →
        M-ell≤ r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤ r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z
          (normTwistedSource W theta) (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    actual_marked_bin_uniform_test a₀ b₀ ha₀ hb₀ Vlog Alog hbox hone
      Lcap eta tau saving em ed hcap heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,C,hCcoef,hC,hbin⟩:=he epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Cm,hCm,hmoment⟩:=reopening_twisted_moment_squared W a₀ b₀ ha₀ hsW hW
    (InverseClippingProfiles.momentOrder (firstDegree degree))
  refine ⟨Ccoef,C*Cm,hCcoef,mul_nonneg hC hCm,?_⟩
  intro theta σ _ S D hbad hSp
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  intro Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbins hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hT:=CanonicalRowCompletion.normTwistedSource_contDiff W a₀ b₀ ha₀ hsW hW theta
  have hsT:Function.support (normTwistedSource W theta)⊆Set.Icc a₀ b₀:=
    (normTwistedSource_support W theta).trans hsW
  have hbnd:=hbin (normTwistedSource W theta) hsT hT S D hbad hSp
    Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbins hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hz:0<Z:=by linarith
  apply hbnd.trans
  calc
    _ ≤ C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
        (Cm*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+
          (volume:Measure ℝ).integrablePower))) :=
      mul_le_mul_of_nonneg_left (hmoment theta hT) (by positivity)
    _ = _ := by ring

end SevenEighths.InverseMoment

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.actual_marked_bin_height_oai := @OAI.SevenEighths.InverseMoment.actual_marked_bin_height_oai
