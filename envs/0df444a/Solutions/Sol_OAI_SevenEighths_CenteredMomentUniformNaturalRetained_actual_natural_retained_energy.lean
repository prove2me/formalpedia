-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentUniformNaturalRetained.actual_natural_retained_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:05:19.197517+00:00
-- url     : https://prove2.me/submissions/e21fd18d-2610-4693-ab71-3a00c8a34a0a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

end CubicReflectionKernel

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

end JointLogSeparation

open scoped BigOperators Classical

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CompletedGauss

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.PolynomialHeight
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

namespace LocalLogFourier

open MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
theorem coupled_positive_log_separation_linear_constant
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℝ → ℂ),
      ContDiffOn ℝ ∞ F (Set.Ioi 0) → ∀ CF : ℝ, 0 ≤ CF →
      (∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ x : ℝ, 0 < x →
        (1 + x)^A * ‖eulerDeriv F i x‖ ≤ CF) →
      ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C * CF ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C * CF) := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P₀ : ℝ := momentConstant K Lwin CW 1
  let B₀ : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P₀ +
    FourierBridge.coefficientMomentBound J P₀)
  let D₀ : ℝ := FourierBridge.fourierPointBound J P₀
  let C₀ : ℝ := (B₀+D₀)/m^A
  have hP₀ : 0 ≤ P₀ := momentConstant_nonneg K Lwin CW 1 hL hCW zero_le_one
  have hB₀ : 0 ≤ B₀ := by
    dsimp [B₀]
    exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 P₀ hP₀)
      (FourierBridge.coefficientMomentBound_nonneg J P₀ hP₀))
  have hD₀ : 0 ≤ D₀ := FourierBridge.fourierPointBound_nonneg J P₀ hP₀
  refine ⟨C₀,by dsimp [C₀]; positivity,?_⟩
  intro F hFpos CF hCF hEuler
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P +
    FourierBridge.coefficientMomentBound J P)
  let Bpoint : ℝ := FourierBridge.fourierPointBound J P
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hPeq : P=P₀*CF := by
    dsimp [P,P₀]
    unfold momentConstant derivativeConstant
    simp only [Finset.sum_mul,Finset.mul_sum,mul_one]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hBeq : B=B₀*CF := by
    dsimp [B,B₀]
    rw [hPeq]
    unfold FourierBridge.coefficientMomentBound
    ring
  have hBpeq : Bpoint=D₀*CF := by
    dsimp [Bpoint,D₀]
    rw [hPeq]
    unfold FourierBridge.fourierPointBound FourierBridge.fourierSeminormBound
    ring
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    have hb : (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ B / m ^ A := by
      simpa [B, P, b, K, Lwin, m] using hbound
    apply hb.trans
    rw [hBeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD₀ : B₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)
  · intro t
    let g := positiveLogProfile V F R hVc hVs hFpos hR
    have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hsource (n : ℕ) (hn : n ≤ J) :
        (m ^ A * (1 + R) ^ A) *
          ((SchwartzMap.seminorm ℝ 0 n) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P := by
      apply positive_log_source_pair V F R m Lwin CW CF P A K n
        hVc hVs hFpos hR hm hm1 hL hCW hCF
      · dsimp [K]; omega
      · exact hVderiv
      · exact hwindow'
      · exact hEuler
      · intro i hi
        exact momentConstant_dominates K i Lwin CW CF hL hCW hCF hi
    have hpoint := FourierBridge.uniform_fourier_pointwise g J
      (m ^ A * (1 + R) ^ A) P (by positivity) hP hsource t
    have hb : (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ Bpoint / m ^ A := by
      apply (le_div_iff₀ (pow_pos hm A)).mpr
      simpa only [g, b, Bpoint, mul_assoc, mul_left_comm, mul_comm] using hpoint
    apply hb.trans
    rw [hBpeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB₀ : D₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)

end LocalLogFourier

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RankMargins
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

open scoped BigOperators Classical SchwartzMap ContDiff

namespace CompletedHeight

section

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

theorem frequencyTwist_finite_uniform_degree (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∀g : 𝓢(ℝ,ℂ), ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤ C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  refine ⟨n,?_⟩
  intro g
  let c : ℕ×ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤ c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤n := Finset.le_sup hz
  exact (frequencyTwist_seminorm_polynomial g t z.1 z.2).trans
    (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn) (by positivity) hC.le)

theorem normTwistedSource_uniform_degree (a b : ℝ) (ha : 0 < a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W ⊆ Icc a b,∀hW : ContDiff ℝ ∞ W,
    ∃C : ℝ,0<C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (uniformTwistedSchwartz W a b ha hs hW t) ≤
        C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (fixedLogReturnCLM a b ha) S
  obtain ⟨n,hn⟩ := frequencyTwist_finite_uniform_degree s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hbound⟩ := hn (CubicReflectionKernel.logSchwartz W a b ha hs hW)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t
  exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDyadic HeckeDetectorFourier

lemma norm_phase (x D : ℝ) (hx : 0<x) (hD : 0<D) (s : ℂ) (t : ℝ) :
    (x : ℂ)^(-s)*FourierBridge.logPhase t (Real.log (x/D)) =
      (D : ℂ)^(-s)*((x/D : ℝ) : ℂ)^(-HeckeDyadic.shift s.re (2*Real.pi*t-s.im)) := by
  have hxD : 0<x/D := div_pos hx hD
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxD.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hD.le,
    ← Complex.ofReal_log hxD.le]
  unfold FourierBridge.logPhase HeckeDyadic.shift
  rw [← Complex.exp_add, ← Complex.exp_add, Real.log_div hx.ne' hD.ne']
  congr 1
  have hs : s=(s.re : ℂ)+(s.im : ℂ)*I := (Complex.re_add_im s).symm
  rw [hs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  push_cast
  ring

lemma polynomial_eq_finite (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (S : Finset (Ideal O))
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ J∈S,
        coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
          (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq) := by
  unfold polynomial
  congr 1
  let f : Ideal O→ℂ := fun J => coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
    (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)
  have hf : Function.support f ⊆ {J : Ideal O | J≠0} := by
    intro J hJ hzero
    subst J
    apply hJ
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have he := tsum_subtype_eq_of_support_subset hf
  change (∑' J : {J : Ideal O // J≠0}, f J.val)=_
  apply he.trans
  apply tsum_eq_sum
  intro J hJ
  by_cases hj : J=0
  · subst J
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have hw : W ((J.absNorm : ℝ)/D)=0 := by
    by_contra hw
    exact hJ (hcover J hj hw)
  simp [f,hw]

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Set
namespace SevenEighths.HeckeDetectorRowwise

theorem norm_sq_le_anchor_integral (F F' : ℝ→ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) {a b x : ℝ} (hx : x∈Icc a b) :
    ‖F x‖^2≤‖F a‖^2+∫ t in a..b, (‖F t‖^2+‖F' t‖^2) := by
  let G : ℝ→ℝ := fun t => ‖F t‖^2+‖F' t‖^2
  have hG : Continuous G := (hF.norm.pow 2).add (hF'.norm.pow 2)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx.1
    (hF.norm.pow 2).continuousOn
    (fun t ht => (hd t).norm_sq.hasDerivWithinAt)
    (hG.continuousOn.integrableOn_Icc)
    (fun t ht => show 2*inner (𝕜:=ℝ) (F t) (F' t)≤G t by
      dsimp [G]
      have hc := real_inner_le_norm (F t) (F' t)
      change (F' t * (starRingEnd ℂ) (F t)).re ≤ ‖F t‖*‖F' t‖ at hc
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)])
  simp only [Pi.pow_apply] at hh
  have hm := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl a) hx.1 hx.2
    (Filter.Eventually.of_forall (fun t => show 0≤G t by dsimp [G]; positivity))
    (hG.intervalIntegrable a b)
  change ‖F x‖^2≤‖F a‖^2+∫ t in a..b, G t
  linarith

theorem rowwise_energy {ι : Type*} (rows : Finset ι) (F F' : ι→ℝ→ℂ)
    (hF : ∀ i∈rows, Continuous (F i)) (hF' : ∀ i∈rows, Continuous (F' i))
    (hd : ∀ i∈rows, ∀ x, HasDerivAt (F i) (F' i x) x)
    (a b E : ℝ) (hab : a≤b) (choice : ι→ℝ)
    (hc : ∀ i∈rows, choice i∈Icc a b)
    (henergy : ∀ t∈Icc a b, ∑ i∈rows, ‖F i t‖^2≤E)
    (henergy' : ∀ t∈Icc a b, ∑ i∈rows, ‖F' i t‖^2≤E) :
    ∑ i∈rows, ‖F i (choice i)‖^2≤(1+2*(b-a))*E := by
  have hg (i : ι) (hi : i∈rows) :
      Continuous (fun t => ‖F i t‖^2+‖F' i t‖^2) :=
    ((hF i hi).norm.pow 2).add ((hF' i hi).norm.pow 2)
  have hs := Finset.sum_le_sum (fun i hi =>
    norm_sq_le_anchor_integral (F i) (F' i) (hF i hi) (hF' i hi) (hd i hi) (hc i hi))
  rw [Finset.sum_add_distrib,←intervalIntegral.integral_finsetSum
    (fun i hi => (hg i hi).intervalIntegrable a b)] at hs
  have hm : (∫ t in a..b, ∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤(b-a)*(2*E) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      ((continuous_finsetSum rows (fun i hi => hg i hi)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => show (∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤2*E by
        rw [Finset.sum_add_distrib]
        linarith [henergy t ht,henergy' t ht])
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have ha := henergy a ⟨le_refl a,hab⟩
  nlinarith

theorem rowwise_energy_two {ι : Type*} (rows : Finset ι)
    (F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ)
    (hcont : ∀ j k i, i∈rows → Continuous (Function.uncurry (F j k i)))
    (hdx : ∀ k i, i∈rows → ∀ x y,
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x)
    (hdy : ∀ j i, i∈rows → ∀ x y,
      HasDerivAt (F j 0 i x) (F j 1 i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (px py : ι→ℝ)
    (hpx : ∀ i∈rows, px i∈Icc a b) (hpy : ∀ i∈rows, py i∈Icc c d)
    (henergy : ∀ j k x, x∈Icc a b → ∀ y, y∈Icc c d →
      ∑ i∈rows, ‖F j k i x y‖^2≤E) :
    ∑ i∈rows, ‖F 0 0 i (px i) (py i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  have cx (j k : Fin 2) (i : ι) (hi : i∈rows) (y : ℝ) :
      Continuous (fun x => F j k i x y) :=
    (hcont j k i hi).comp (continuous_id.prodMk continuous_const)
  have cy (j k : Fin 2) (i : ι) (hi : i∈rows) (x : ℝ) :
      Continuous (F j k i x) :=
    (hcont j k i hi).comp (continuous_const.prodMk continuous_id)
  have he (j : Fin 2) (x : ℝ) (hx : x∈Icc a b) :
      ∑ i∈rows, ‖F j 0 i x (py i)‖^2≤(1+2*(d-c))*E :=
    rowwise_energy rows (fun i => F j 0 i x) (fun i => F j 1 i x)
      (fun i hi => cy j 0 i hi x) (fun i hi => cy j 1 i hi x)
      (fun i hi y => hdy j i hi x y) c d E hcd py hpy
      (fun y hy => henergy j 0 x hx y hy) (fun y hy => henergy j 1 x hx y hy)
  exact rowwise_energy rows (fun i x => F 0 0 i x (py i))
    (fun i x => F 1 0 i x (py i))
    (fun i hi => cx 0 0 i hi (py i)) (fun i hi => cx 1 0 i hi (py i))
    (fun i hi x => hdx 0 i hi x (py i)) a b ((1+2*(d-c))*E) hab px hpx
    (he 0) (he 1)

end SevenEighths.HeckeDetectorRowwise

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeDetectorRowwise

theorem scaleProfile_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    Continuous (scaleProfile W) := by
  have hd := hW.continuous_deriv (by simp)
  unfold scaleProfile
  fun_prop

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos l).ne'),
    ←Complex.ofReal_log (Real.exp_pos l).le,Real.log_exp]
  congr 1
  ring

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwise
open ConcretePrimeRowBridge hiding O

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

theorem reflected_profile_height_control (a b : ℝ) (ha : 0<a) (A K : ℕ) :
    ∃ n : ℕ,∀ (W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t : ℝ,∀j : ℕ,j≤K → ∀x : ℝ,0≤x →
      (1+x)^A*‖LocalLogFourier.eulerDeriv
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) j x‖≤C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  obtain ⟨n,hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDbd⟩ := hn W hs hW
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t j hj x hx
  have hsame : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext y
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t y
  have hb := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) j hj x hx
  rw [hsame] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (hDbd t) hC.le).trans_eq (by ring))
end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ScaleSupremum
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)

lemma scaleTest_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (j : Fin 2) :
    Continuous (scaleTest W j) := by
  unfold scaleTest
  split
  · exact hW.continuous
  · exact scaleProfile_continuous W hW

end SevenEighths.CenteredMomentScaleSupremum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentFrequencyScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge FourierBridge
open CenteredMomentScaleSupremum (scaleTest scaleTest_continuous scaleTest_support)
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)

theorem frequencyScaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (frequencyScaleSum χ inv W freq S) := by
  unfold frequencyScaleSum
  fun_prop

theorem frequencyScaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (frequencyScaleSum χ inv W freq S) (frequencyScaleSum χ inv (scaleProfile W) freq S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert (preTransparency := .instances) ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-t)))
        ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert (preTransparency := .instances) ((hW _).hasDerivAt.scomp l hy).const_mul ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))) using 1
    · rfl
    · change (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert (preTransparency := .instances) hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [frequencyScaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [frequencyScaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

lemma ratio_frequency_phase (x l freq : ℝ) (hx : 0<x) :
    (((x/Real.exp l : ℝ):ℂ)^(-_root_.OAI.SevenEighths.HeckeDyadic.shift 0 freq))=
      logPhase (freq/(2*Real.pi)) (-l)*logPhase (freq/(2*Real.pi)) (Real.log x) := by
  have ht : 2*Real.pi*(freq/(2*Real.pi))=freq := by field_simp
  have hh := norm_phase x (Real.exp l) hx (Real.exp_pos l) 0 (freq/(2*Real.pi))
  rw [ht] at hh
  simp only [neg_zero,Complex.cpow_zero,one_mul,zero_re,zero_im,sub_zero] at hh
  rw [←hh,Real.log_div hx.ne' (Real.exp_pos l).ne',Real.log_exp]
  rw [show Real.log x-l=(-l)+Real.log x by ring,logPhase_add]

theorem frequencyScaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    polynomial χ inv W (Real.exp l) 0 freq=
      logPhase (freq/(2*Real.pi)) (-l)*frequencyScaleSum χ inv W freq S l := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 freq S hc,scale_normalization]
  unfold frequencyScaleSum
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h0 : J=0
  · subst J
    simp only [coefficient_zero,zero_mul,mul_zero]
  have hpos : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h0)
  rw [ratio_frequency_phase _ l freq hpos,Real.exp_neg,div_eq_mul_inv]
  ring

theorem frequencyScaleSum_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    ‖frequencyScaleSum χ inv W freq S l‖=‖polynomial χ inv W (Real.exp l) 0 freq‖ := by
  rw [frequencyScaleSum_eq_polynomial χ inv W freq S l hc,norm_mul,logPhase_norm,one_mul]

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 (freq₁ i) *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 (freq₂ i) * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x *
      frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    frequencyScaleSum_norm (χ i) false (scaleTest W j) (freq₁ i) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    frequencyScaleSum_norm (ψ i) false (scaleTest V k) (freq₂ i) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((frequencyScaleSum_continuous (χ i) false _ (freq₁ i) S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((frequencyScaleSum_continuous (ψ i) false _ (freq₂ i) T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (frequencyScaleSum_deriv (χ i) false W (freq₁ i) S (hW.differentiable (by simp)) x).mul_const
        (frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((frequencyScaleSum_deriv (ψ i) false V (freq₂ i) T (hV.differentiable (by simp)) y).const_mul
        (frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,norm_mul,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert (preTransparency := .instances) hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  simp only [norm_mul]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

end SevenEighths.CenteredMomentFrequencyScaleSupremum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedProfileMeasure
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedProfileMeasure
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem actual_profile_separation (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier (CompletedHeight.normTwistedSource W t)
          (s*Real.exp y)=∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨n,hn⟩ := CenteredMomentComparisonReflection.reflected_profile_height_control
    a b ha A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨(C+1)*D,by positivity,?_⟩
  intro t s hs0
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : ContDiffOn ℝ ∞ (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Set.Ioi 0) := by
    rw [←he]
    exact paperRadialFourier_contDiffOn _
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep _ hF (D*(1+‖t‖)^n) (by positivity)
    (fun j hj x hx=>hDb t j hj x hx.le) s hs0
  refine ⟨density,?_,hi,hm.trans ?_,fun v=>(hp v).trans ?_⟩
  · intro y
    simpa using hid (fun _ : Unit=>y)
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]

theorem row_density_energy {ι : Type*} [Fintype ι]
    (density φ : ι→ℝ→ℂ) (rho : ℝ→ℝ) (w : ℝ→ℝ)
    (hrho : ∀v,0< rho v) (hw : ∀v,0<w v)
    (hpoint : ∀i v,‖density i v‖≤ rho v)
    (hint : ∀i,Integrable (fun v=>density i v*φ i v))
    (hmeasure : Integrable (fun v=>rho v*w v))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀v,(∑i,‖φ i v‖^2)≤E*(w v)^2) :
    (∑i,‖∫v : ℝ,density i v*φ i v‖^2)≤E*(∫v : ℝ,rho v*w v)^2 := by
  let B (v : ℝ) : ℂ := (rho v*w v:ℝ)
  let F (i : ι) (v : ℝ) : ℂ := density i v/B v*φ i v
  have hB0 (v : ℝ) : B v≠0 := Complex.ofReal_ne_zero.mpr (mul_pos (hrho v) (hw v)).ne'
  have hBn (v : ℝ) : ‖B v‖=rho v*w v := by
    exact Complex.norm_of_nonneg (mul_pos (hrho v) (hw v)).le
  have he (i : ι) (v : ℝ) : B v*F i v=density i v*φ i v := by
    dsimp only [F]
    field_simp [hB0 v]
  have hFn (i : ι) (v : ℝ) : ‖F i v‖≤‖φ i v‖/w v := by
    dsimp only [F]
    rw [norm_mul,norm_div,hBn]
    calc
      _≤(rho v/(rho v*w v))*‖φ i v‖ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hpoint i v) (mul_pos (hrho v) (hw v)).le) (norm_nonneg _)
      _=_ := by field_simp [(hrho v).ne', (hw v).ne']
  have hb (v : ℝ) : (∑i,‖F i v‖^2)≤E := by
    calc
      _≤∑i,(‖φ i v‖/w v)^2 := Finset.sum_le_sum (fun i _=>
        pow_le_pow_left₀ (norm_nonneg _) (hFn i v) 2)
      _=(∑i,‖φ i v‖^2)/(w v)^2 := by simp only [div_pow,Finset.sum_div]
      _≤E := (div_le_iff₀ (sq_pos_of_pos (hw v))).mpr (henergy v)
  have hh := CompletedGauss.finite_integral_energy_bound B F E hE
    (by simpa only [hBn] using hmeasure) (fun i=>by simpa only [he] using hint i) hb
  simpa only [he,hBn] using hh

theorem finite_annular_separation (V F : ℝ→ℂ) (s X : ℝ) (hX : 0<X)
    (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v)
    (η : Character) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0)
    (hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  have hnorm (I : Ideal O) (hI : I∈S) : 0<(I.absNorm:ℝ)/X := by
    apply div_pos _ hX
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
  have hi (I : Ideal O) : Integrable (fun v : ℝ=>
      density v*(HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    have ht := ((density.integrable (μ:=volume)).mul_bdd
      (logPhase_continuous_left (Real.log ((I.absNorm:ℝ)/X))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v=>le_of_eq (logPhase_norm v _)))).mul_const
        (HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X))
    apply ht.congr
    filter_upwards [] with v
    ring
  have hp (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 0 S
    (fun I hI h=>hc I hI (mul_ne_zero_iff.mp h).1)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_self,neg_zero,
    Complex.cpow_zero,mul_one]
  simp_rw [hp]
  have he : (fun v : ℝ=>density v*((X:ℂ)^(-(1/2:ℂ))*
      ∑I∈S,HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) =
      (fun v=>(X:ℂ)^(-(1/2:ℂ))*∑I∈S,density v*(HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    funext v
    rw [←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum S (fun I _=>hi I)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hh := hsep (Real.log ((I.absNorm:ℝ)/X))
  rw [Real.exp_log (hnorm I hI)] at hh
  simp only [logWindow,if_pos (hnorm I hI)]
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

lemma logWindow_support (V : ℝ→ℂ) (M : ℝ)
    (hV : ∀y,V y≠0 → |y|≤M) :
    Function.support (logWindow V)⊆Set.Icc (Real.exp (-M)) (Real.exp M) := by
  intro x hx
  change logWindow V x≠0 at hx
  by_cases hxp : 0<x
  · have hv : V (Real.log x)≠0 := by simpa only [logWindow,if_pos hxp] using hx
    have hh := abs_le.mp (hV _ hv)
    constructor
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.1
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.2
  · exact False.elim (hx (by simp only [logWindow,if_neg hxp]))

theorem plain_annular_separation (V F : ℝ→ℂ) (M s X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v) (η : Character) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  exact finite_annular_separation V F s X hX density hsep η S hs hc

end SevenEighths.CenteredMomentReflectedProfileMeasure

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedPairEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedPairEnergy
open HeckeFamily FourierBridge CenteredMomentReflectedProfileMeasure
local notation "O" => HeckeFamily.O

lemma plain_frequency_control (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) :
    Continuous (fun v : ℝ=>HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
    ∃K : ℝ,∀v : ℝ,‖HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)‖≤K := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  have he (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hs I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  constructor
  · simp_rw [he]
    exact continuous_const.mul (continuous_finsetSum S (fun I _=>
      continuous_const.mul (logPhase_continuous_left _)))
  · refine ⟨‖(X:ℂ)^(-(1/2:ℂ))‖*∑I∈S,
      ‖HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)‖,?_⟩
    intro v
    rw [he,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul,logPhase_norm,mul_one]

lemma plain_density_integrable (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) (density : 𝓢(ℝ,ℂ)) :
    Integrable (fun v : ℝ=>density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) := by
  obtain ⟨hc,K,hK⟩ := plain_frequency_control V M X hX hV η
  exact (density.integrable (μ:=volume)).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)

end SevenEighths.CenteredMomentReflectedPairEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedUniformPair
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedUniformPair
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy

lemma heightScale_pos (A n : ℕ) (s t : ℝ) (hs : 0<s) : 0<heightScale A n s t := by
  unfold heightScale
  positivity

lemma envelope_pos (C : ℝ) (hC : 0<C) (J : ℕ) (v : ℝ) : 0<envelope C J v := by
  unfold envelope
  positivity

lemma envelope_weight (C : ℝ) (J : ℕ) (v : ℝ) :
    envelope C J v*(1+‖v‖)^J=C/(1+v^2) := by
  unfold envelope
  field_simp

lemma envelope_integrable (C : ℝ) (J : ℕ) :
    Integrable (fun v : ℝ=>envelope C J v*(1+‖v‖)^J) := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  exact integrable_inv_one_add_sq.const_mul C

lemma envelope_integral (C : ℝ) (J : ℕ) :
    (∫v : ℝ,envelope C J v*(1+‖v‖)^J)=C*Real.pi := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  rw [integral_const_mul,integral_univ_inv_one_add_sq]

lemma normalized_density_bound (A n J : ℕ) (s t C : ℝ) (hs : 0<s)
    (b : 𝓢(ℝ,ℂ))
    (hp : ∀v : ℝ,(1+s)^A*(1+‖v‖)^(J+2)*‖b v‖≤C*(1+‖t‖)^n) :
    ∀v : ℝ,‖(((heightScale A n s t:ℝ):ℂ) • b) v‖≤envelope C J v := by
  intro v
  have ht : 0<(1+‖t‖)^n := by positivity
  have hv : 0<(1+‖v‖)^J := by positivity
  have hh : (1+‖v‖)^2*((1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖)≤C := by
    rw [smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (heightScale_pos A n s t hs).le]
    unfold heightScale
    have hh := (div_le_iff₀ ht).mpr (hp v)
    convert (preTransparency := .instances) hh using 1 ; rw [pow_add] ; ring
  have hnorm : 0≤(1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖ := by positivity
  have hb := CubicReflectionKernel.weighted_two_to_cauchy hnorm v hh
  apply (le_div_iff₀ hv).mpr
  simpa only [envelope,mul_comm] using hb

end SevenEighths.CenteredMomentReflectedUniformPair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectionDeletion
open HeckeFamily CenteredMomentComparisonReflection UniqueFactorizationMonoid
open IdealMobiusDivisorSum EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma subset_product_nonzero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

lemma subset_product_moebius (D : Finset (Ideal O)) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D,P) : ℂ) = (-1 : ℂ)^D.card := by
  have hf : normalizedFactors (∏ P ∈ D,P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D,P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

end SevenEighths.CenteredMomentReflectionDeletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.TwistedReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentTwistedReflection
open HeckeFamily CenteredMomentNaturalPrimitive
open CenteredMomentReflectionDeletion EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma polynomial_twisted_source (χ : Character) (W : ℝ→ℂ) (X t : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      HeckeDyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm := HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (HeckeDyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [HeckeDyadic.norm,HeckeDyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

end SevenEighths.CenteredMomentTwistedReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionEnergy
open HeckeFamily CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentComparisonReflection
open EisensteinSchwartzPoisson

lemma polynomial_inverse_plain (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false W X 0 0=
      conj (HeckeDyadic.polynomial χ false (fun x=>conj (W x)) X 0 0) := by
  rw [polynomial_plain _ _ _ hX,polynomial_plain _ _ _ hX,map_mul,map_inv₀,
    Complex.conj_ofReal,Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro I
  rw [map_mul,idealCoeff_inverse_conj,Complex.conj_conj]

theorem actual_one_uniform (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s t X Y omega : ι→ℝ)(Wshort : ℝ→ℂ),
        (∀i,0<s i) → (∀i,0<X i) →
      ∀E : ℝ,0≤E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V W A n (s i) (t i)) (X i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤C*E := by
  obtain ⟨n,hn⟩ := actual_profile_separation V M a b hM hV ha A (J+2)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨(C*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s t X Y omega Wshort hs hX E hE henergy
  choose d hid hi hm hp using fun i=>hb (t i) (s i) (hs i)
  let e (i : ι) : ℂ := heightScale A n (s i) (t i)
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (CompletedHeight.normTwistedSource W (t i)) x
  let Q (i : ι) := HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*Q i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*FourierBridge.logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*FourierBridge.logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*FourierBridge.logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (normalizedReflected V W A n (s i) (t i)) (X i) 0 0*Q i=
      ∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : normalizedReflected V W A n (s i) (t i)=
        (fun x=>logWindow V x*F i (s i*x)) := by
      funext x
      dsimp [normalizedReflected,F,e]
      ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (Q i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope C J)
    (fun v=>(1+‖v‖)^J) (envelope_pos C hC J) (by intro v;positivity)
    (fun i=>normalized_density_bound A n J (s i) (t i) C (hs i) (d i) (hp i)) hint
    (envelope_integrable C J) E hE (by
      intro v
      simpa only [φ,Q,mul_assoc] using henergy v)
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  simpa only [Q,mul_assoc,mul_comm E] using hh

end SevenEighths.CenteredMomentOneReflectionEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentReflectedAnnuli
open Set EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentComparisonReflection LocalLogFourier

theorem logWindow_support : Function.support logWindow ⊆ Icc (-Real.log 4) 0 := by
  intro v hv
  have hn : annulus (Real.exp v) ≠ 0 := by simpa [logWindow] using hv
  have hlow : 1/4 < Real.exp v := lt_of_not_ge (fun h => hn (annulus_zero_low _ h))
  have hhigh : Real.exp v < 1 := lt_of_not_ge (fun h => hn (annulus_zero_high _ h))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  constructor
  · exact (Real.exp_lt_exp.mp (hl ▸ hlow)).le
  · exact (Real.exp_lt_one_iff.mp hhigh).le

theorem annularMass_nonneg (B : ℕ) (n : ℤ) : 0≤annularMass B n := by
  have hp := dyadicScale_pos n
  unfold annularMass
  positivity

lemma sqrt_nat_pow (x : ℝ) (hx : 0≤x) (j : ℕ) :
    Real.sqrt (x^j)=(Real.sqrt x)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx j),ih,pow_succ]

theorem annularMass_lower_bound (B j : ℕ) :
    annularMass B (-(j:ℤ))≤(Real.sqrt (1/2:ℝ))^j := by
  have hx := dyadicScale_pos (-(j:ℤ))
  have hd : 1≤(1+dyadicScale (-(j:ℤ)))^B := one_le_pow₀ (by linarith)
  have he : dyadicScale (-(j:ℤ))=(1/2:ℝ)^j := by
    simp [dyadicScale,zpow_neg,inv_pow]
  calc
    annularMass B (-(j:ℤ))≤Real.sqrt (dyadicScale (-(j:ℤ))) :=
      div_le_self (Real.sqrt_nonneg _) hd
    _=(Real.sqrt (1/2:ℝ))^j := by rw [he,sqrt_nat_pow _ (by norm_num)]

theorem annularMass_upper_bound (B A j : ℕ) (hAB : A+1≤B) :
    annularMass B (j:ℤ)≤((2:ℝ)^A)⁻¹^j := by
  have hx : 1≤dyadicScale (j:ℤ) := by
    simp only [dyadicScale,zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hp : 0<dyadicScale (j:ℤ) := dyadicScale_pos _
  have hd : dyadicScale (j:ℤ)^(A+1)≤(1+dyadicScale (j:ℤ))^B :=
    (pow_le_pow_left₀ hp.le (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hAB)
  have hb : annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := by
    unfold annularMass
    exact div_le_div₀ hp.le (Real.sqrt_le_self_iff.mpr (Or.inr hx))
      (by positivity) hd
  calc
    annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := hb
    _=((2:ℝ)^A)⁻¹^j := by
      rw [pow_succ,mul_comm (dyadicScale (j:ℤ)^A),div_mul_cancel_left₀ (ne_of_gt hp)]
      simp only [dyadicScale,zpow_natCast,←pow_mul,inv_pow]
      rw [Nat.mul_comm]

lemma nonnegative_geometric_tail (f : ℕ→ℝ) (q : ℝ) (hq0 : 0≤q) (hq1 : q<1)
    (hf : ∀j,0≤f j) (hb : ∀j,f j≤q^j) (L : ℕ) :
    Summable (fun j=>f (j+L)) ∧ (∑'j:ℕ,f (j+L))≤q^L/(1-q) := by
  have hg : Summable (fun j:ℕ=>q^(j+L)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq1).mul_right (q^L)
  have hs := Summable.of_nonneg_of_le (fun j=>hf (j+L)) (fun j=>hb (j+L)) hg
  refine ⟨hs,(hs.tsum_le_tsum (fun j=>hb (j+L)) hg).trans_eq ?_⟩
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1]
  ring

theorem annularMass_lower_tail (B L : ℕ) :
    Summable (fun j:ℕ=>annularMass B (-((j+L:ℕ):ℤ))) ∧
      (∑'j:ℕ,annularMass B (-((j+L:ℕ):ℤ)))≤
        (Real.sqrt (1/2:ℝ))^L/(1-Real.sqrt (1/2:ℝ)) := by
  apply nonnegative_geometric_tail (fun j=>annularMass B (-(j:ℤ)))
    (Real.sqrt (1/2:ℝ)) (Real.sqrt_nonneg _)
    (by simpa using (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
    (fun j=>annularMass_nonneg _ _) (annularMass_lower_bound B) L

theorem annularMass_upper_tail (B A L : ℕ) (hA : 1≤A) (hAB : A+1≤B) :
    Summable (fun j:ℕ=>annularMass B ((j+L:ℕ):ℤ)) ∧
      (∑'j:ℕ,annularMass B ((j+L:ℕ):ℤ))≤
        (((2:ℝ)^A)⁻¹)^L/(1-((2:ℝ)^A)⁻¹) := by
  have hp : 1<(2:ℝ)^A := by
    calc
      1<(2:ℝ)^1 := by norm_num
      _≤(2:ℝ)^A := pow_le_pow_right₀ (by norm_num) hA
  apply nonnegative_geometric_tail (fun j=>annularMass B (j:ℤ))
    ((2:ℝ)^A)⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hp)
    (fun j=>annularMass_nonneg _ _) (fun j=>annularMass_upper_bound B A j hAB) L

theorem annularMass_summable (B : ℕ) (hB : 2≤B) : Summable (annularMass B) := by
  apply Summable.of_nat_of_neg
  · simpa only [Nat.add_zero] using (annularMass_upper_tail B 1 0 (by omega) hB).1
  · simpa only [Nat.add_zero] using (annularMass_lower_tail B 0).1

end SevenEighths.CenteredMomentReflectedAnnuli

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentReflectedNormalization
open HeckeFamily CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson

lemma actual_log_window :
    CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow=
      (fun x : ℝ=>(annulus x:ℂ)) := by
  funext x
  unfold CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow
  split_ifs with hx
  · rw [Real.exp_log hx]
  · rw [annulus_zero_low x (by linarith)]
    rfl

lemma polynomial_const (χ : Character) (W : ℝ→ℂ) (X : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X 0 0=
      c*HeckeDyadic.polynomial χ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  have he (I : HeckeDyadic.NonzeroIdeal) :
      HeckeDyadic.summand χ false (fun x=>c*W x) X 0 0 I=
        c*HeckeDyadic.summand χ false W X 0 0 I := by
    unfold HeckeDyadic.summand
    ring
  simp_rw [he,tsum_mul_left]
  ring

lemma normalized_profile_actual (W : ℝ→ℂ) (B n : ℕ) (s t x : ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n s t x=
      (heightScale B n s t:ℂ)*CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) s x := by
  unfold normalizedReflected
  rw [actual_log_window]
  unfold CenteredMomentReflectedAnnuli.annularProfile
  ring

theorem actual_annular_normalization (χ : Character) (W : ℝ→ℂ) (B n : ℕ)
    (k : ℤ) (t Y : ℝ) :
    (Real.sqrt (dyadicScale k):ℂ)*HeckeDyadic.polynomial χ false
      (CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k))
      (dyadicScale k*Y) 0 0=
      (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
        HeckeDyadic.polynomial χ false
          (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t)
          (dyadicScale k*Y) 0 0 := by
  have hf : normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t=
      (fun x=>(heightScale B n (dyadicScale k) t:ℂ)*
        CenteredMomentReflectedAnnuli.annularProfile
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k) x) :=
    funext (normalized_profile_actual W B n (dyadicScale k) t)
  rw [hf,polynomial_const]
  have hh : (1+‖t‖)^n*CenteredMomentReflectedAnnuli.annularMass B k*
      heightScale B n (dyadicScale k) t=Real.sqrt (dyadicScale k) := by
    unfold CenteredMomentReflectedAnnuli.annularMass heightScale
    have ht : (1+‖t‖)^n≠0 := ne_of_gt (by positivity)
    have hs : (1+dyadicScale k)^B≠0 := ne_of_gt (by have := dyadicScale_pos k;positivity)
    field_simp
  have hc : (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
      (heightScale B n (dyadicScale k) t:ℂ)=(Real.sqrt (dyadicScale k):ℂ) := by
    rw [←Complex.ofReal_mul,←Complex.ofReal_mul,hh]
  rw [←mul_assoc _ (heightScale B n (dyadicScale k) t:ℂ),hc]

end SevenEighths.CenteredMomentReflectedNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization
open CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by
  intro x hx
  have hn : annulus x≠0 := by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

end SevenEighths.CenteredMomentOneReflectionScaleEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedTruncation
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedTruncation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open CenteredMomentReflectedSeries EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma retainedAnnuli_mem (R Y : ℝ) (hY : 0<Y) (n : ℤ) :
    n∈retainedAnnuli R Y hY ↔ Retained R n ∧ ∃q : ℝ,Y⁻¹≤q ∧ dyadicWeight n q≠0 := by
  exact (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).mem_toFinset

end SevenEighths.CenteredMomentReflectedTruncation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionMass
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

lemma weight_nonneg (I : Ideal O) : 0 ≤ weight I := by unfold weight; positivity
lemma weight_mul (I J : Ideal O) : weight (I*J) = weight I * weight J := by
  simp only [weight, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv_rev]
  ring
lemma weight_one : weight (1 : Ideal O) = 1 := by simp [weight]
lemma weight_pow (I : Ideal O) (n : ℕ) : weight (I ^n) = weight I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using weight_one
  | succ n ih => rw [pow_succ,weight_mul,ih,pow_succ]
lemma weight_prod (S : Finset (Ideal O)) (f : Ideal O → Ideal O) :
    weight (∏ P ∈ S,f P) = ∏ P ∈ S,weight (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weight_one
  | @insert P S h ih => simp only [Finset.prod_insert h,weight_mul,ih]
lemma prime_weight_lt_one (P : Ideal O) (hP : Prime P) : weight P < 1 := by
  have h : (1:ℝ) < P.absNorm := by
    have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
    exact_mod_cast (by omega : 1 < P.absNorm)
  have hs : 1 < Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  exact inv_lt_one_of_one_lt₀ hs

lemma reconstruct_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    (∏ P : S,P.val ^ exponents S I P) = I.val.val := by
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P)]
  exact (Finset.prod_multiset_count_of_subset (normalizedFactors I.val.val) S I.property).symm.trans
    (Ideal.prod_normalizedFactors_eq_self I.val.property)
lemma exponents_injective (S : Finset (Ideal O)) : Function.Injective (exponents S) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  rw [← reconstruct_exponents S I,← reconstruct_exponents S J,h]
lemma weight_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    weight I.val.val = ∏ P : S,weight P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P => weight P ^ (normalizedFactors I.val.val).count P), weight_prod]
  simp only [weight_pow]

lemma hasSum_geometric_pi {α : Type*} [Fintype α] (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a < 1) :
    HasSum (fun n : α → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹) := by
  classical
  apply Fintype.induction_empty_option (P := fun β _ => ∀ (r : β → ℝ),
    (∀ a, 0 ≤ r a) → (∀ a, r a < 1) →
    HasSum (fun n : β → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹)) ?_ ?_ ?_ α r hr hr1
  · intro α β _ e ih r hr hr1
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (r ∘ e) (fun a => hr (e a)) (fun a => hr1 (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he := E.hasSum_iff.mpr h
    convert (preTransparency := .instances) he using 1
    · funext n
      exact (e.prod_comp (fun b => r b ^ n b)).symm
    · exact (e.prod_comp (fun b => (1-r b)⁻¹)).symm
  · intro r _ _
    simp
  · intro α _ ih r hr hr1
    have h0 := hasSum_geometric_of_lt_one (hr none) (hr1 none)
    have ht := ih (fun a => r (some a)) (fun a => hr (some a)) (fun a => hr1 (some a))
    have hs := h0.summable.mul_of_nonneg ht.summable (fun n => pow_nonneg (hr none) n)
      (fun n => Finset.prod_nonneg (fun a _ => pow_nonneg (hr (some a)) (n a)))
    have hp := h0.mul ht hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hp
    simpa only [Function.comp_def, Fintype.prod_option, Equiv.piOptionEquivProd_apply] using he

lemma smooth_summable (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    Summable (fun I : SmoothIdeal S => weight I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr (fun I => (weight_exponents S I).symm)

lemma smooth_mass_le_euler (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    (∑' I : SmoothIdeal S,weight I.val.val) ≤ ∏ P ∈ S,(1-weight P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg (fun P _ => pow_nonneg (weight_nonneg P.val) (n P)))
    (fun I => (weight_exponents S I).le) (smooth_summable S hS) hh.summable
  rw [hh.tsum_eq,Finset.prod_coe_sort S (fun P => (1-weight P)⁻¹)] at h
  exact h

lemma deletion_mass (S : Finset (Ideal O)) :
    (∑ D ∈ S.powerset, weight (∏ P ∈ D,P)) = ∏ P ∈ S,(1+weight P) := by
  simp_rw [weight_prod]
  exact (Finset.prod_one_add S).symm

lemma localMass_nonneg (P : Ideal O) (hP : Prime P) : 0 ≤ localMass P := by
  exact div_nonneg (by linarith [weight_nonneg P]) (sub_pos.mpr (prime_weight_lt_one P hP)).le
lemma prime_weight_le (P : Ideal O) (hP : Prime P) : weight P ≤ 3/4 := by
  have hn : (2:ℝ) ≤ P.absNorm := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩ : 2 ≤ P.absNorm)
  have hs : 4/3 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
  nlinarith
lemma localMass_le_seven (P : Ideal O) (hP : Prime P) : localMass P ≤ 7 := by
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith [prime_weight_le P hP]
lemma localMass_le_three (P : Ideal O) (hP : Prime P) (hn : (4:ℝ) ≤ P.absNorm) :
    localMass P ≤ 3 := by
  have hs : 2 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hw : weight P ≤ 1/2 := by
    rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
    linarith
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith

theorem euler_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P),
      (∏ P ∈ S,localMass P) ≤ C * (Ideal.absNorm (∏ P ∈ S,P) : ℝ)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3:ℝ)))
  let K : ℕ := ⌈max 4 B⌉₊
  let smallIdeals := ConcretePrimeRowBridge.idealsUpTo K
  have hK : max 4 B ≤ (K:ℝ) := Nat.le_ceil _
  refine ⟨(7:ℝ)^smallIdeals.card,by positivity,?_⟩
  intro S hS
  have hpoint (P : Ideal O) (hP : P ∈ S) :
      localMass P ≤ (if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε := by
    have hn : (1:ℝ) ≤ P.absNorm := by
      have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hS P hP⟩
      exact_mod_cast (by omega : 1 ≤ P.absNorm)
    have he : 1 ≤ (P.absNorm:ℝ)^ε := Real.one_le_rpow hn hε.le
    by_cases hp : P ∈ smallIdeals
    · simp only [if_pos hp]
      exact (localMass_le_seven P (hS P hP)).trans (by nlinarith)
    · have hpk : (K:ℝ) < P.absNorm := by
        have hh : ¬ P.absNorm ≤ K := by
          intro h
          apply hp
          exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr ⟨by exact_mod_cast hn,h⟩
        exact_mod_cast Nat.lt_of_not_ge hh
      have h4 : (4:ℝ) ≤ P.absNorm := (le_max_left _ _).trans (hK.trans hpk.le)
      have hb : B ≤ (P.absNorm:ℝ) := (le_max_right _ _).trans (hK.trans hpk.le)
      simp only [if_neg hp,one_mul]
      exact (localMass_le_three P (hS P hP) h4).trans (hB _ hb)
  have hc : (S.filter (· ∈ smallIdeals)).card ≤ smallIdeals.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    (∏ P ∈ S,localMass P) ≤ ∏ P ∈ S,((if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε) :=
      Finset.prod_le_prod (fun P hP => localMass_nonneg P (hS P hP)) hpoint
    _ = (7:ℝ)^(S.filter (· ∈ smallIdeals)).card * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
      rw [Finset.prod_mul_distrib,← Finset.prod_filter]
      simp only [Finset.prod_const,Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod,Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc) (Real.rpow_nonneg (by positivity) _)

lemma coefficient_norm_le (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (hD : ∀ P ∈ D,Prime P) (H : SmoothIdeal S) :
    ‖coefficient η ηi S D H‖ ≤ weight (∏ P ∈ D,P) * weight H.val.val := by
  rw [coefficient,subset_product_moebius D hD]
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖idealCoeff η (∏ P ∈ D,P)‖ * ‖idealCoeff ηi H.val.val‖ ≤ 1 :=
    (mul_le_mul (idealCoeff_norm_le_one η _) (idealCoeff_norm_le_one ηi _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [CenteredMomentReflectionDeletion.norm,weight,Real.sqrt_mul (Nat.cast_nonneg _),one_div,mul_inv_rev]
  ring

lemma coefficient_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient η ηi S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hD hP)) H

lemma coefficient_mass_le_euler (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
      ∏ P ∈ S,localMass P := by
  have hD (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        weight (∏ P ∈ D,P) * (∏ P ∈ S,(1-weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm η ηi S hS D hsub).tsum_le_tsum
      (fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hsub hP)) H)
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul,deletion_mass,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

lemma coefficient_mass_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) := by
  exact summable_sum (fun D hD => coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD))

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P)
      (η ηi : Character),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := euler_mass_subpower ε hε
  exact ⟨C,hC,fun S hS η ηi => ⟨coefficient_mass_summable η ηi S hS,
    (coefficient_mass_le_euler η ηi S hS).trans (hbound S hS)⟩⟩

end SevenEighths.CenteredMomentReflectionMass
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionTailMass
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectionTailMass
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma subset_norm_le (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S) :
    (Ideal.absNorm (∏P∈D,P):ℝ)≤(Ideal.absNorm (∏P∈S,P):ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS)))
    (map_dvd Ideal.absNorm (Finset.prod_dvd_prod_of_subset D S (fun P=>P) hD))

lemma restoration_norm_one (S : Finset (Ideal O)) (H : SmoothIdeal S) : 1≤norm H.val := by
  unfold CenteredMomentReflectionDeletion.norm
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr H.val.property))

end SevenEighths.CenteredMomentReflectionTailMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive
open CenteredMomentTwistedReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma radical_le_original (χ ψ : Character)
    (hcap : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm) :
    (Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by
  have hp : 1≤ψ.modulus.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact_mod_cast (show (redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm by
    nlinarith)

end SevenEighths.CenteredMomentOriginalReflectionApproximation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionLength
namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentComparisonReflection

lemma reflected_scale_bound (Z M n xi C Q R d h s : ℝ)
    (hZ : 1<Z) (_hC : 0≤C) (hQ : 0≤Q) (hd : 0≤d) (_hs : 0≤ s)
    (hcap : Q*R≤C*Z^M) (hdR : d≤R) (hh : 1≤h) (hsmax : s≤Z^(xi/2)) :
    s*(Q*d/(Z^n*h))≤C*Z^(M-n+xi/2) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : 0<Z^n := Real.rpow_pos_of_pos hz _
  have hp : Q*d≤C*Z^M := (mul_le_mul_of_nonneg_left hdR hQ).trans hcap
  have hy : Q*d/(Z^n*h)≤C*Z^M/Z^n := by
    calc
      _≤Q*d/Z^n := div_le_div_of_nonneg_left (mul_nonneg hQ hd) hn (by nlinarith)
      _≤C*Z^M/Z^n := div_le_div_of_nonneg_right hp hn.le
  calc
    _≤Z^(xi/2)*(C*Z^M/Z^n) := mul_le_mul hsmax hy (by positivity) (by positivity)
    _=C*Z^(M-n+xi/2) := by
      rw [Real.rpow_add hz,Real.rpow_sub hz]
      ring

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0<Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M a Q R d h : ℝ),
      0<Q → 0<d → Q*R≤C*Z^M → d≤R → 1≤h →
      ∀n : ℤ,∀hY : 0<Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0<xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0<Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentReflectionRetainedLength

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionWeightedEnergy
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentReflectedAnnuli
local notation "O" => HeckeFamily.O

lemma signedWeight_norm (η ηi : Character) (S : Finset (Ideal O))
    (B : ℕ) (a : Index S) :
    ‖signedWeight η ηi S B a‖ =
      ‖coefficient η ηi S a.1.1.val a.1.2‖ * annularMass B a.2 := by
  rw [signedWeight,norm_mul,Complex.norm_real,Real.norm_of_nonneg (annularMass_nonneg _ _)]

lemma annularMass_le_two (B : ℕ) (hB : 2≤B) (n : ℤ) :
    annularMass B n ≤ annularMass 2 n := by
  have hp := CenteredMomentSectorLocalization.dyadicScale_pos n
  unfold annularMass
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by linarith [CenteredMomentSectorLocalization.dyadicScale_pos n]) hB)

lemma coefficient_joint_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    Summable (fun a : S.powerset × SmoothIdeal S =>
      ‖coefficient η ηi S a.1.val a.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun D => coefficient_summable_norm η ηi S hS D.val
    (Finset.mem_powerset.mp D.property),(hasSum_fintype _).summable⟩

lemma coefficient_joint_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    (∑' a : S.powerset × SmoothIdeal S,‖coefficient η ηi S a.1.val a.2‖) =
      ∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖ := by
  rw [(coefficient_joint_summable η ηi S hS).tsum_prod,tsum_fintype]
  exact Finset.sum_coe_sort S.powerset (fun D => ∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)

lemma signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) := by
  simp_rw [signedWeight_norm]
  exact (coefficient_joint_summable η ηi S hS).mul_of_nonneg
    (annularMass_summable B hB) (fun _ => norm_nonneg _) (annularMass_nonneg B)

lemma signedWeight_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    (∑'a : Index S,‖signedWeight η ηi S B a‖) =
      (∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖) *
        ∑'n : ℤ,annularMass B n := by
  rw [(signedWeight_summable_norm η ηi S hS B hB).tsum_prod]
  simp_rw [signedWeight_norm,tsum_mul_left]
  rw [tsum_mul_right,coefficient_joint_mass η ηi S hS]

lemma signed_series_reindex (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (f : Index S→ℂ) (hs : Summable (fun a=>‖signedWeight η ηi S B a*f a‖)) :
    (∑'a : Index S,signedWeight η ηi S B a*f a) =
      ∑D : S.powerset,∑'H : SmoothIdeal S,∑'n : ℤ,
        coefficient η ηi S D.val H*(annularMass B n:ℂ)*f ((D,H),n) := by
  rw [hs.of_norm.tsum_prod,hs.of_norm.prod.tsum_prod,tsum_fintype]
  rfl

theorem signed_mass_subpower (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(∑'n : ℤ,annularMass B n) := by
  obtain ⟨C,hC,hb⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi B hB
  refine ⟨signedWeight_summable_norm η ηi S hS B hB,?_⟩
  rw [signedWeight_mass η ηi S hS B hB]
  exact mul_le_mul_of_nonneg_right (hb S hS η ηi).2 (tsum_nonneg (annularMass_nonneg B))

lemma annularConstant_pos : 0<annularConstant := by
  have h : 0≤∑'n : ℤ,annularMass 2 n := tsum_nonneg (annularMass_nonneg 2)
  dsimp [annularConstant]
  linarith

lemma annularMass_total_le (B : ℕ) (hB : 2≤B) :
    (∑'n : ℤ,annularMass B n) ≤ annularConstant := by
  apply ((annularMass_summable B hB).tsum_le_tsum (annularMass_le_two B hB)
    (annularMass_summable 2 le_rfl)).trans
  dsimp [annularConstant]
  linarith

theorem uniform_signed_mass (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := signed_mass_subpower ε hε
  refine ⟨C*annularConstant,mul_pos hC annularConstant_pos,?_⟩
  intro S hS η ηi B hB
  refine ⟨(hb S hS η ηi B hB).1,(hb S hS η ηi B hB).2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (annularMass_total_le B hB) (by positivity)).trans_eq (by ring)

lemma sum_iSup_le_of_selection {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (g : ∀i,α i→ℝ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,g i (a i))≤E) :
    (∑i,⨆a,g i a)≤E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/((Fintype.card ι:ℝ)+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  choose a ha using fun i => exists_lt_of_lt_ciSup
    (show (⨆a,g i a)-δ < (⨆a,g i a) by linarith)
  have hh : (∑i,⨆a,g i a) ≤ ∑i,(g i (a i)+δ) := by
    apply Finset.sum_le_sum
    intro i _
    linarith [ha i]
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  have he : ((Fintype.card ι:ℝ)+1)*δ=ε := by
    dsimp [δ]
    field_simp
  have hn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  have hb := hselection a
  simp only [Finset.card_univ] at hh
  nlinarith

lemma selection_point_bound {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (f : ∀i,α i→ℂ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) (i : ι) (a : α i) :
    ‖f i a‖^2≤E := by
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>‖f j (Function.update base i a j)‖^2)
    (fun j _=>sq_nonneg _) (Finset.mem_univ i)
  exact (by simpa using hh : ‖f i a‖^2≤∑j,‖f j (Function.update base i a j)‖^2).trans
    (hselection (Function.update base i a))

theorem weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (w f : ∀i,α i→ℂ) (M E : ℝ) (_hM : 0≤M)
    (hs : ∀i,Summable (fun a=>‖w i a‖))
    (hm : ∀i,(∑'a,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∀i,Summable (fun a=>‖w i a*f i a‖)) ∧
      (∑i,‖∑'a,w i a*f i a‖^2)≤M^2*E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  let v (i : ι) : ℝ := ⨆a,‖f i a‖^2
  have hbd (i : ι) : BddAbove (Set.range (fun a=>‖f i a‖^2)) :=
    ⟨E,by rintro _ ⟨a,rfl⟩;exact selection_point_bound base f E hselection i a⟩
  have hv (i : ι) (a : α i) : ‖f i a‖^2≤v i := le_ciSup (hbd i) a
  have hv0 (i : ι) : 0≤v i := (sq_nonneg _).trans (hv i (base i))
  have hnorm (i : ι) (a : α i) : ‖f i a‖≤Real.sqrt (v i) :=
    (Real.le_sqrt (norm_nonneg _) (hv0 i)).mpr (hv i a)
  have hw (i : ι) : Summable (fun a=>‖w i a*f i a‖) := by
    apply ((hs i).mul_right (Real.sqrt (v i))).of_nonneg_of_le (fun _=>norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _)
  have hsum (i : ι) : ‖∑'a,w i a*f i a‖≤M*Real.sqrt (v i) := by
    apply (norm_tsum_le_tsum_norm (hw i)).trans
    apply ((hw i).tsum_le_tsum (fun a=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _))
      ((hs i).mul_right (Real.sqrt (v i)))).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm i) (Real.sqrt_nonneg _)
  refine ⟨hw,?_⟩
  calc
    (∑i,‖∑'a,w i a*f i a‖^2) ≤ ∑i,(M*Real.sqrt (v i))^2 :=
      Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hsum i) 2)
    _ = M^2*∑i,v i := by simp only [mul_pow,Real.sq_sqrt (hv0 _),Finset.mul_sum]
    _ ≤ M^2*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun i a=>‖f i a‖^2) E hselection) (sq_nonneg M)

lemma masked_signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    Summable (fun a=>‖mask a*signedWeight η ηi S B a‖) := by
  apply (signedWeight_summable_norm η ηi S hS B hB).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

lemma masked_signedWeight_mass_le (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    (∑'a,‖mask a*signedWeight η ηi S B a‖)≤∑'a,‖signedWeight η ηi S B a‖ := by
  apply (masked_signedWeight_summable_norm η ηi S hS B hB mask hm).tsum_le_tsum
    _ (signedWeight_summable_norm η ηi S hS B hB)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

theorem actual_masked_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀(mask f : ∀i,Index (S i)→ℂ),(∀i a,‖mask i a‖≤1) →
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖)) ∧
      (∑i,‖∑'a,(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖^2) ≤
        C*R^ε*E := by
  obtain ⟨C,hC,hb⟩ := uniform_signed_mass (ε/2) (by positivity)
  refine ⟨C ^2,sq_pos_of_pos hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap mask f hmask hselection
  have hR0 : 0≤R := by linarith
  let M := C*R^(ε/2)
  have hM : 0≤M := by dsimp [M];positivity
  have hs (i : ι) := masked_signedWeight_summable_norm (η i) (ηi i) (S i)
    (hS i) (B i) (hB i) (mask i) (hmask i)
  have hm (i : ι) :
      (∑'a,‖mask i a*signedWeight (η i) (ηi i) (S i) (B i) a‖)≤M := by
    apply (masked_signedWeight_mass_le (η i) (ηi i) (S i) (hS i) (B i) (hB i)
      (mask i) (hmask i)).trans
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0≤ε/2)) hC.le
  have hh := weighted_selection_energy (fun i=>baseIndex (S i))
    (fun i a=>mask i a*signedWeight (η i) (ηi i) (S i) (B i) a) f M E hM hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr : (R^(ε/2))^2=R^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  dsimp [M]
  rw [mul_pow,hr]

theorem actual_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀f : ∀i,Index (S i)→ℂ,
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖)) ∧
      (∑i,‖∑'a,signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖^2)≤C*R^ε*E := by
  obtain ⟨C,hC,h⟩ := actual_masked_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap f hselection
  simpa only [norm_one,one_mul] using
    h S hS η ηi B hB R E hR hcap (fun _ _=>1) f (by intro i a;simp) hselection

end SevenEighths.CenteredMomentReflectionWeightedEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ReflectedChoiceEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectedChoiceEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentReflectionDeletion CenteredMomentReflectionTailMass
open CenteredMomentNaturalPrimitive CenteredMomentReflectionRetainedLength
open Filter

local notation "O" => HeckeFamily.O

theorem eventually_natural_choice_geometry (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      let S := redundantSet χ.modulus ψ.modulus
      ∀u : Index S,
      let Y := (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈u.1.1.val,P):ℝ)/(Z^a*CenteredMomentReflectionDeletion.norm u.1.2.val)
      ∀hY : 0<Y,u.2∈retainedAnnuli (Z^(xi/4)) Y hY →
      1≤dyadicScale u.2*Y ∧
      0≤Real.log (dyadicScale u.2*Y) ∧
      Real.log (dyadicScale u.2*Y)≤(M-a+xi)*Real.log Z := by
  filter_upwards [eventually_actual_retained_length C 1 xi hC le_rfl hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod
  dsimp only
  intro u hY hu
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hD := subset_product_norm_pos u.1.1.val
    (fun P hP=>hS P ((Finset.mem_powerset.mp u.1.1.property) hP))
  have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤C*Z^M := by
    have hh : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by exact_mod_cast hcap
    exact hh.trans hmod
  have hh := hZ.2 M a _ _ _ _ hQ hD hc
    (subset_norm_le _ _ hS (Finset.mem_powerset.mp u.1.1.property))
    (restoration_norm_one _ u.1.2) u.2 hY hu
  simp only [one_mul] at hh
  refine ⟨hh.1,Real.log_nonneg hh.1,?_⟩
  have hz : 0<Real.log Z := Real.log_pos hZ.1
  have hlog := hh.2.2
  rw [Real.logb] at hlog
  exact (div_le_iff₀ hz).mp hlog

end SevenEighths.CenteredMomentReflectedChoiceEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentRetainedWeightedSource
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectedNormalization
open CenteredMomentReflectedAnnuli CenteredMomentReflectedTruncation
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem finiteAnnularColumn_normalized (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H)*P =
    (((1+‖t‖)^n:ℝ):ℂ)*∑'k : ℤ,(annularMass B k:ℂ)*
      retainedColumn χ ψ W X R t hX B n P ((D,H),k) := by
  rw [finiteAnnularColumn,dif_pos (dualScale_pos χ ψ X hX D H),
    tsum_eq_sum (s:=retainedAnnuli R (dualScale χ ψ X D H) (dualScale_pos χ ψ X hX D H))
      (fun k hk=>by simp only [retainedColumn,if_neg hk,mul_zero]),
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [retainedColumn,if_pos hk,actual_annular_normalization]
  ring

theorem retainedOriginal_eq_weighted (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖)) :
    retainedOriginal χ ψ W X R t*P =
      (((1+‖t‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes χ ψ),
        signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
          retainedColumn χ ψ W X R t hX B n P a := by
  rw [signed_series_reindex ψ ψ.inverse (sourcePrimes χ ψ) B _ hs]
  change (∑D∈(sourcePrimes χ ψ).powerset,∑'H : SmoothIdeal (sourcePrimes χ ψ),
    coefficient ψ ψ.inverse (sourcePrimes χ ψ) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
        R ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)))*P = _
  rw [←Finset.sum_coe_sort (sourcePrimes χ ψ).powerset,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [←tsum_mul_right,←tsum_mul_left]
  apply tsum_congr
  intro H
  change (coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H))*P = _
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [mul_assoc,tsum_mul_left]
  ring

theorem retainedOriginal_fiber_summable (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖))
    (D : (sourcePrimes χ ψ).powerset) :
    Summable (fun H : SmoothIdeal (sourcePrimes χ ψ)=>
      ‖(coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
        finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
          R (dualScale χ ψ X D H))*P‖) := by
  have hh := ((hs.of_norm.prod.prod_factor D).mul_left (((1+‖t‖)^n:ℝ):ℂ)).norm
  apply hh.congr
  intro H
  congr 1
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [signedWeight,mul_assoc,tsum_mul_left]
  ring

theorem actual_retained_weighted_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(χ ψ : ι→Character)(W : ι→ℝ→ℂ)(X R t : ι→ℝ)
        (hX : ∀i,0<X i)(B : ι→ℕ)(n : ℕ)(P : ι→ℂ),
      (∀i,2≤B i) → ∀(T Rcap E : ℝ),0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀a : ∀i,Index (sourcePrimes (χ i) (ψ i)),
        (∑i,‖retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) (a i)‖^2)≤E) →
      (∀i,Summable (fun a : Index (sourcePrimes (χ i) (ψ i))=>
        ‖signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
          retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a‖)) ∧
      (∀i,retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i =
        (((1+‖t i‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes (χ i) (ψ i)),
          signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
            retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a) ∧
      (∀i,∀D : (sourcePrimes (χ i) (ψ i)).powerset,
        Summable (fun H : SmoothIdeal (sourcePrimes (χ i) (ψ i))=>
          ‖(coefficient (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) D.val H*
            finiteAnnularColumn (χ i).inverse
              (paperRadialFourier (CompletedHeight.normTwistedSource (W i) (t i)))
              (R i) (dualScale (χ i) (ψ i) (X i) D H))*P i‖)) ∧
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2) ≤
        C*Rcap^ε*(1+T)^(2*n)*E := by
  obtain ⟨C,hC,hbound⟩ := actual_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ ψ W X R t hX B n P hB T Rcap E hT ht hRcap hcap hselection
  let f (i : ι) := retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i)
  have he := hbound (fun i=>sourcePrimes (χ i) (ψ i))
    (fun i=>redundantSet_prime (χ i).modulus (ψ i).modulus) ψ (fun i=>(ψ i).inverse)
    B hB Rcap E hRcap hcap f hselection
  have hid (i : ι) := retainedOriginal_eq_weighted (χ i) (ψ i) (W i) (X i) (R i) (t i)
    (hX i) (B i) n (P i) (he.1 i)
  refine ⟨he.1,hid,?_,?_⟩
  · intro i D
    exact retainedOriginal_fiber_summable (χ i) (ψ i) (W i) (X i) (R i) (t i)
      (hX i) (B i) n (P i) (he.1 i) D
  · let z (i : ι) := ∑'a : Index (sourcePrimes (χ i) (ψ i)),
        signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*f i a
    have hn (i : ι) :
        ‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖=(1+‖t i‖)^n*‖z i‖ := by
      rw [hid i,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    have hp (i : ι) : (1+‖t i‖)^n≤(1+T)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith [ht i]) n
    calc
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2)
          = ∑i,((1+‖t i‖)^n*‖z i‖)^2 := by simp_rw [hn]
      _ ≤ ∑i,((1+T)^n*‖z i‖)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)) 2
      _ = ((1+T)^n)^2*∑i,‖z i‖^2 := by simp only [mul_pow,Finset.mul_sum]
      _ ≤ ((1+T)^n)^2*(C*Rcap^ε*E) := mul_le_mul_of_nonneg_left he.2 (sq_nonneg _)
      _ = C*Rcap^ε*(1+T)^(2*n)*E := by rw [←pow_mul,Nat.mul_comm n 2];ring

end SevenEighths.CenteredMomentRetainedWeightedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentUniformReflectionProfile
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentOneReflectionEnergy

theorem source_separation (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀G : 𝓢(ℝ,ℂ),∀D : ℝ,0<D →
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤D → ∀s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier G (s*Real.exp y)=
          ∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*D ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*D) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨H,K,hK,hEuler⟩ := paperRadialFourier_euler_source_weighted_bound
    A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨H,(C+1)*K,by positivity,?_⟩
  intro G D hD hGD s hs
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep (paperRadialFourier G)
    (paperRadialFourier_contDiffOn G) (K*D) (by positivity)
    (fun j hj x hx=>(hEuler G j hj x hx.le).trans
      (mul_le_mul_of_nonneg_left hGD hK.le)) s hs
  have hconst : C*(K*D)≤((C+1)*K)*D := by nlinarith [mul_pos hK hD]
  exact ⟨density,(fun y=>by simpa using hid (fun _ : Unit=>y)),hi,
    hm.trans hconst,fun v=>(hp v).trans hconst⟩

theorem actual_one_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,K,hK,hb⟩ := source_separation V M hM hV A (J+2)
  refine ⟨H,(K*Real.pi)^2,by positivity,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  choose d hid hi hm hp using fun i=>hb (G i) D hD (hGD i) (s i) (hs i)
  let e (i : ι) : ℂ := (1+s i)^A
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (G i) x
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (X i) 0 0*P i=∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))=
        (fun x=>logWindow V x*F i (s i*x)) := by funext x;dsimp [F,e];ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (P i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hpoint (i : ι) : ∀v,‖(e i • d i) v‖≤envelope (K*D) J v := by
    have hh := normalized_density_bound A 0 J (s i) 0 (K*D) (hs i) (d i)
      (by simpa using hp i)
    simpa [heightScale,e] using hh
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope (K*D) J)
    (fun v=>(1+‖v‖)^J) (envelope_pos (K*D) (mul_pos hK hD) J)
    (by intro v;positivity) hpoint hint (envelope_integrable (K*D) J) E hE henergy
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  convert (preTransparency := .instances) hh using 1
  ring

lemma inverse_annular_frequency (χ : Character) (V : ℝ→ℂ)
    (hreal : ∀y,conj (V y)=V y) (X v : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false (logWindow V) X 0 (2*Real.pi*v)=
      conj (HeckeDyadic.polynomial χ false (logWindow V) X 0 (-2*Real.pi*v)) := by
  have hr (x : ℝ) : conj (logWindow V x)=logWindow V x := by
    unfold logWindow
    split_ifs <;> simp [hreal]
  have ht : (fun x=>conj (CompletedHeight.normTwistedSource (logWindow V) v x))=
      CompletedHeight.normTwistedSource (logWindow V) (-v) := by
    funext x
    simp only [CompletedHeight.normTwistedSource,map_mul,hr]
    exact congrArg (fun z=>z*logWindow V x) (SecondPassIntegration.logPhase_conjugate v _)
  rw [CenteredMomentTwistedReflection.polynomial_twisted_source χ.inverse _ X v hX,
    polynomial_inverse_plain χ _ X hX,ht,
    ←CenteredMomentTwistedReflection.polynomial_twisted_source χ _ X (-v) hX]
  congr 2
  ring

theorem actual_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,C,hC,hbound⟩ := actual_one_uniform V M hM hV A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  apply hbound G (fun i=>(χ i).inverse) P s X hs hX D E hD hE hGD
  intro v
  have he (i : ι) :
      ‖HeckeDyadic.polynomial (χ i).inverse false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖=
      ‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖ := by
    rw [inverse_annular_frequency (χ i) V hreal (X i) v (hX i),norm_mul,
      Complex.norm_conj,←norm_mul]
  simpa only [he] using henergy v

end SevenEighths.CenteredMomentUniformReflectionProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformReflectionScale
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentUniformReflectionScale
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentOneReflectionScaleEnergy CenteredMomentUniformReflectionProfile
open CenteredMomentReflectedNormalization

theorem actual_rowwise_scales (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)
      (s lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Set.Icc lo hi) → (∀i,ly i∈Set.Icc low high) →
      (∀i,0<s i) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  have hreal : ∀y,conj (CenteredMomentReflectedAnnuli.logWindow y)=
      CenteredMomentReflectedAnnuli.logWindow y := by
    intro y
    exact Complex.conj_ofReal _
  obtain ⟨H,C,hC,hbound⟩:=actual_inverse_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow hreal A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly hspos hD hE hGD henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i) false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        (polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    rw [actual_log_window]
    simp only [←mul_assoc]
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by rw [←pow_mul,Nat.mul_comm J 2]
    apply hh.trans_eq
    rw [hp]
    ring
  have hh:=hbound G χ (fun i=>polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)
    s (fun i=>Real.exp (lx i)) hspos (fun i=>Real.exp_pos _) D
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) hD (mul_nonneg hdx (mul_nonneg hdy hE)) hGD hfixed
  simp only [actual_log_window,←mul_assoc] at hh
  convert (preTransparency := .instances) hh using 1

end SevenEighths.CenteredMomentUniformReflectionScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformReflectionChoices
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionChoices
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionScale

theorem actual_independent_choices (B J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0<s i u) → (∀i u,keep i u → 0<X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i (u i))^B:ℂ)*paperRadialFourier (G i) (s i (u i)*x))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_rowwise_scales B J
  refine ⟨H,C,hC,?_⟩
  intro ι _ α G χ P s X keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hD hE hGD henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb G χ P' (fun i=>s i (u i)) lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=>hspos i (u i)) hD hE hGD he
  convert (preTransparency := .instances) hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

end SevenEighths.CenteredMomentUniformReflectionChoices

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformRetainedEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformRetainedEnergy
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionChoices CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentReflectedUniformPair
open CenteredMomentReflectedNormalization

lemma twisted_zero (W:ℝ→ℂ) : CompletedHeight.normTwistedSource W 0=W := by
  funext x
  simp [CompletedHeight.normTwistedSource,FourierBridge.logPhase]

lemma normalized_zero (G:𝓢(ℝ,ℂ)) (B:ℕ) (s:ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow G B 0 s 0=
      (fun x=>(annulus x:ℂ)*((1+s)^B:ℂ)*paperRadialFourier G (s*x)) := by
  funext x
  simp only [normalizedReflected,heightScale,pow_zero,div_one,twisted_zero,actual_log_window]
  push_cast
  rfl

lemma retained_zero (χ ψ:Character) (G:𝓢(ℝ,ℂ)) (X R:ℝ) :
    retainedOriginal χ ψ G X R 0=retainedSchwartz χ ψ G X R := by
  unfold retainedOriginal retainedSchwartz
  rw [twisted_zero]

theorem actual_retained_uniform_energy (epsilon : ℝ)
    (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(X R ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high D E Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := actual_independent_choices B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R ly omega Wshort c d lo hi low high D E Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp G χ P s Y keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hD hE hGD henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) (G i) (X i) (R i) 0 (hX i) B 0 (P' i) (u i)‖^2)≤
        Cp*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,normalized_zero,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun i=>(G i:ℝ→ℂ)) X R (fun _=>0) hX (fun _=>B) 0 P' (fun _=>hB)
    0 Rcap _ le_rfl (fun _=>by simp) hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [retained_zero,P',Nat.mul_zero,pow_zero,mul_one,←mul_assoc] at hfinal
  convert (preTransparency := .instances) hfinal using 1 ; ring

end SevenEighths.CenteredMomentUniformRetainedEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.UniformNaturalRetained
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformNaturalRetained
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentUniformRetainedEnergy CenteredMomentUniformReflectionApproximation CenteredMomentRetainedWeightedSource
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy_oai (epsilon Cscale xi : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort D E Rcap : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_retained_uniform_energy epsilon hepsilon B J hB
  refine ⟨H,C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ G χ ψ P omega Wshort c d M along bshort D E Rcap hd hshort hshortsmooth
    hnatural hmod hD hE hGD hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hlog : 0≤Real.log Z := (Real.log_pos hZ.1).le
  have hexp : Real.exp (bshort*Real.log Z)=Z^bshort := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  have hgeom (i : ι) (u : Index (sourcePrimes (χ i) (ψ i)))
      (hY : 0<dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)
      (hu : u.2∈CenteredMomentReflectedTruncation.retainedAnnuli (Z^(xi/4))
        (dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2) hY) :
      Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)∈
        Set.Icc 0 (max 0 (M-along+xi)*Real.log Z) := by
    have hh := hZ.2 (χ i) (ψ i) M along (hnatural i) (hmod i) u hY hu
    exact ⟨hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩
  have hrad (i : ι) : (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap :=
    (radical_le_original (χ i) (ψ i) (hnatural i)).trans (hcap i)
  have hh := hb G χ ψ P (fun _=>Z^along) (fun _=>Z^(xi/4)) (fun _=>bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    D E Rcap (fun _=>Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hD hE hGD hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh

end SevenEighths.CenteredMomentUniformNaturalRetained

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentUniformNaturalRetained.actual_natural_retained_energy_oai := @OAI.SevenEighths.CenteredMomentUniformNaturalRetained.actual_natural_retained_energy_oai
