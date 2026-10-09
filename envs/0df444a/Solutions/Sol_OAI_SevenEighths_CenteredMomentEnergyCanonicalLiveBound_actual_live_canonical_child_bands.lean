-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound.actual_live_canonical_child_bands
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:07:00.03064+00:00
-- url     : https://prove2.me/submissions/6929ee8c-e2c2-4409-8112-8ebe2be7c990

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCapacityRemoval_actual_state_capacity_removal

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
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
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.InverseContour
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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem logPullbackCLM_apply (a b : ℝ) (W : SchwartzMap ℝ ℂ) (u : ℝ) :
    logPullbackCLM a b W u = logCutoff a b u • W (patchedExp a b u) := by
  rw [logPullbackCLM, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
    ((logCutoff a b).hasCompactSupport.hasTemperateGrowth (logCutoff a b).contDiff)]
  rfl

theorem logCutoff_eq_one_of_source (a b : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : Real.exp u ∈ Set.Icc a b) : logCutoff a b u = 1 := by
  apply (logCutoff a b).one_of_mem_closedBall
  have hl := Real.log_le_log ha hu.1
  have hr := Real.log_le_log (Real.exp_pos u) hu.2
  simp only [Real.log_exp] at hl hr
  change dist u 0 ≤ logRadius a b
  rw [Real.dist_eq, sub_zero]
  apply abs_le.mpr
  constructor <;> dsimp [logRadius] <;>
    linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem patchedExp_eq_exp_of_cutoff_ne_zero (a b u : ℝ) (hu : logCutoff a b u ≠ 0) :
    patchedExp a b u = Real.exp u := by
  have hmem : u ∈ Function.support (logCutoff a b) := hu
  rw [(logCutoff a b).support_eq] at hmem
  have heta : logOuterCutoff a b u = 1 := by
    apply (logOuterCutoff a b).one_of_mem_closedBall
    change dist u 0 ≤ logRadius a b + 1
    change dist u 0 < logRadius a b + 1 at hmem
    exact le_of_lt hmem
  simp [patchedExp, expCorrection, heta]

theorem logPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    logPullbackCLM a b W u = W (Real.exp u) := by
  rw [logPullbackCLM_apply]
  by_cases hW : W (Real.exp u) = 0
  · by_cases hcut : logCutoff a b u = 0
    · simp [hcut, hW]
    · rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u hcut, hW, smul_zero]
  · have hcut := logCutoff_eq_one_of_source a b ha u (hsupp hW)
    rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u (by rw [hcut]; norm_num), hcut, one_smul]

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Height
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentHeight
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open QuadraticInitialBound CenteredMomentLattice
open CenteredMomentPrimary CenteredMomentTwist

lemma normalized_height_le (t : ℝ) : ‖t / (2 * Real.pi)‖ ≤ ‖t‖ := by
  rw [norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])

end SevenEighths.CenteredMomentHeight
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeHeight
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeight
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem rowTwistedSum_eq (η χ : Character) (m A₀ z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]

end SevenEighths.CenteredMomentHeckeHeight

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RetainedProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem seminorm_dilation_le (f g : 𝓢(ℝ, ℂ)) (ζ : ℂ) (c B : ℝ)
    (hζ : ‖ζ‖ = 1) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hg : ∀ x, g x = ζ * f (c * x)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n g ≤ B ^ n * SchwartzMap.seminorm ℝ k n f := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hB0 : 0 ≤ B := hc0.trans hcB
  have he : (g : ℝ → ℂ) = fun x => ζ * f (c * x) := funext hg
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (by positivity)
  intro x
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f.smooth n), norm_mul, hζ,
    one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 n)]
  have hx : |x| ^ k ≤ |c * x| ^ k := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  calc
    _ = c ^ n * (|x| ^ k * ‖iteratedDeriv n f (c * x)‖) := by ring
    _ ≤ c ^ n * (|c * x| ^ k * ‖iteratedDeriv n f (c * x)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (pow_nonneg hc0 n)
    _ ≤ c ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k n f (c * x))
        (pow_nonneg hc0 n)
    _ ≤ B ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcB _) (apply_nonneg _ _)

theorem normPowerProfile_dilated (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    normPowerProfile (dilated W c) (a / B) b
      (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t x =
      ((c : ℂ) ^ (Complex.I * t))⁻¹ *
        normPowerProfile W a b ha hs hW t (c * x) := by
  rw [normPowerProfile_apply, normPowerProfile_apply]
  by_cases hz : W (c * x) = 0
  · simp [dilated, hz]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hx : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha (hs hz).1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  have hp := Complex.mul_cpow_ofReal_nonneg hc0.le hx.le (Complex.I * t)
  rw [← Complex.ofReal_mul] at hp
  rw [hp]
  have hn : (c : ℂ) ^ (Complex.I * t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_real_imaginary_power c t hc0]; norm_num)
  dsimp only [dilated]
  simp only [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem normPowerProfile_dilated_seminorm (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n (normPowerProfile W a b ha hs hW t) := by
  apply seminorm_dilation_le _ _ ((c : ℂ) ^ (Complex.I * t))⁻¹ c B
    (by rw [norm_inv, norm_real_imaginary_power c t (lt_of_lt_of_le zero_lt_one hc), inv_one])
    hc hcB
  intro x
  exact normPowerProfile_dilated W a b B c ha hB hc hcB hs hW t x

theorem normPowerProfile_dilated_finite (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (F : Finset (ℕ × ℕ)) :
    F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) := by
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  apply (normPowerProfile_dilated_seminorm W a b B c ha hB hc hcB hs hW t z.1 z.2).trans
  exact mul_le_mul (pow_le_pow_right₀ hB (Finset.le_sup hz))
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hz) (apply_nonneg _ _) (by positivity)

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,mul_assoc]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily

attribute [local instance] OAI.SevenEighths.HeckeFamily.instIsPrincipalIdealRingO_solutions
theorem elementCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (n : O) :
    elementCoeff (η.refineModulus M hM hle) n =
      if IsUnit (Ideal.Quotient.mk M n) then elementCoeff η n else 0 :=
  ResidueCharacter.inflate_mk hle η.residue n

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlotShift
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma norm_height_split (N D σ t v:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ v))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ (t+v)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_add]
  ring

end SevenEighths.CenteredMomentPrimeSlotShift

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SlotNormalization
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤X) (hP:∀i,0≤P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (fun i _=>hP i),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤X₁*X₂) (hP:∀i,0≤P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  calc
    _=((Real.sqrt (X₁*X₂):ℂ)⁻¹*(∏i,(Real.sqrt (P i):ℂ)⁻¹))*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏i,rowSlot η m A z (S i) (β i) t) := by ring
    _=_ := by rw [he]

end SevenEighths.CenteredMomentSlotNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,idealCoeff χ I*W ((I.absNorm:ℝ)/X) at he
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,HeckeDyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

theorem plain_polynomial_eq_row (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (X σ t : ℝ) (hX : 0<X) :
    polynomial χ false W X σ t = (Real.sqrt X:ℂ)⁻¹*
      rowTwistedSum η m A z (twistProfile W σ t) 0 X := by
  rw [←polynomial_twistProfile,plain_zero_height _ _ X hX,rowTwistedSum_eq η χ m A z hrow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveSlotRow_eq_product
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t) S β P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,normalizedSlot η m A z (S i) (β i) 0 (P i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open FourierBridge JointLogSeparation CompletedHeight CenteredMomentLattice
open EisensteinSchwartzPoisson

theorem frequencyTwist_source_control (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (g : 𝓢(ℝ, ℂ)) (t : ℝ),
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤
          C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g * (1 + ‖t‖)^n := by
  let T := S.biUnion fun z => (Finset.range (z.2+1)).image fun i => (z.1,i)
  let c : ℕ × ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*(z.2+1)
  let C := 1 + ∑ z ∈ S, c z
  have hc (z) : 0 ≤ c z := by dsimp [c]; positivity
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z)
    dsimp [C]; linarith
  refine ⟨S.sup Prod.snd,T,C,hC,?_⟩
  intro g t
  have hder (z) (hz : z ∈ S) : derivativeSeminormSum g z.1 z.2 ≤
      (z.2+1:ℝ) * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
    calc
      _ ≤ ∑ i ∈ Finset.range (z.2+1), T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := by
        apply Finset.sum_le_sum
        intro i hi
        apply Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) (i := (z.1,i))
        exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
      _ = _ := by simp
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z ≤ C := by
    have := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]; linarith
  calc
    _ ≤ ((2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2) *
        (1+‖t‖)^z.2 := frequencyTwist_seminorm_polynomial g t z.1 z.2
    _ ≤ (c z * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^z.2 := by
      dsimp only [c]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hder z hz)
          (show 0 ≤ (2:ℝ)^z.2*(1+2*Real.pi)^z.2 by positivity))
        (show 0 ≤ (1+‖t‖)^z.2 by positivity)).trans_eq (by ring)
    _ ≤ (C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) g) *
        (1+‖t‖)^(S.sup Prod.snd) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hzC (apply_nonneg _ _)
      · exact pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)
      · positivity
      · positivity

theorem normPowerProfile_source_control (a b : ℝ) (ha : 0 < a)
    (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ W : 𝓢(ℝ, ℂ), ∀ hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b,
      ∀ t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        C * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := schwartzCLM_finite_seminorm_control (fixedLogReturnCLM a b ha) S
  obtain ⟨n,S₂,C₂,hC₂,h₂⟩ := frequencyTwist_source_control S₁
  obtain ⟨T,C₃,hC₃,h₃⟩ := schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM a b) S₂
  refine ⟨n,T,C₁*C₂*C₃,by positivity,?_⟩
  intro W hs t
  have heq : CubicReflectionKernel.logSchwartz W a b ha hs (W.smooth ⊤) =
      CubicReflectionKernel.logPullbackCLM a b W := by
    ext u
    rw [CubicReflectionKernel.logSchwartz_apply,
      CubicReflectionKernel.logPullbackCLM_eq_actual a b ha W hs]
  have ht : (1+‖t/(2*Real.pi)‖)^n ≤ (1+‖t‖)^n := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  unfold normPowerProfile uniformTwistedSchwartz
  rw [heq]
  calc
    _ ≤ C₁ * S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (CubicReflectionKernel.logPullbackCLM a b W) (t/(2*Real.pi))) := h₁ _
    _ ≤ C₁ * (C₂ * (C₃ * T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (1+‖t‖)^n) := by
      apply mul_le_mul_of_nonneg_left _ hC₁.le
      exact (h₂ _ _).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (h₃ W) hC₂.le) ht (by positivity) (by positivity))
    _ = _ := by ring
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceMask
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma coprime_support_iff (I R : Ideal O) (hR : R≠0) :
    (∀P∈primeSupport R,IsCoprime I P) ↔ IsCoprime I R := by
  constructor
  · intro h
    have aux : ∀s : Multiset (Ideal O),(∀P∈s,IsCoprime I P)→IsCoprime I s.prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simpa using (isCoprime_one_right : IsCoprime I 1)
      | @cons a s ih =>
        intro hs
        rw [Multiset.prod_cons]
        exact (hs a (Multiset.mem_cons_self _ _)).mul_right
          (ih (fun P hP=>hs P (Multiset.mem_cons_of_mem hP)))
    rw [←Ideal.prod_normalizedFactors_eq_self hR]
    exact aux _ (fun P hP=>h P (Multiset.mem_toFinset.mpr hP))
  · intro h P hP
    exact h.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

lemma excluded_ideal (χ : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I=if IsCoprime I R then idealCoeff χ I else 0 := by
  simp only [excluded,idealCoeff_excludePrimes,coprime_support_iff I R hR]

lemma excluded_element (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime (Ideal.span {n}) R then elementCoeff χ n else 0 := by
  by_cases hn : n=0
  · subst n
    have hh : elementCoeff (excluded χ R) 0=0 := by
      rw [excluded,Character.excludePrimes,elementCoeff_refineModulus,hχ0]
      split_ifs <;> rfl
    rw [hh,hχ0]
    split_ifs <;> rfl
  · rw [←idealCoeff_span _ hn,excluded_ideal χ R hR,idealCoeff_span χ hn]

lemma excluded_element_generator (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime n (idealGenerator R) then elementCoeff χ n else 0 := by
  rw [excluded_element χ hχ0 R hR]
  conv_lhs => rw [←span_idealGenerator R,Ideal.isCoprime_span_singleton_iff]

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

lemma NaturalRow.ideal {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff F.character I=idealCoeff η I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

lemma NaturalRow.element_zero {η : Character} {z : O} (F : NaturalRow η z) :
    elementCoeff F.character 0=0 := by
  rw [F.element]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (0:Ideal O)=0
  rw [(idealRowHom (fixedBadMask^6*1^4*z)).map_zero,mul_zero]

lemma NaturalRow.masked_element {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded F.character R) n=
      rowTwist (elementHom η) (fixedBadMask*idealGenerator R) 1 z n := by
  rw [excluded_element_generator F.character F.element_zero R hR,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask (idealGenerator R) 1 z n
      (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

lemma NaturalRow.masked_ideal {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded F.character R) I=
      idealCoeff η I*idealRowHom ((fixedBadMask*idealGenerator R)^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η (excluded F.character R)
    (fixedBadMask*idealGenerator R) 1 z (F.masked_element R hR) I

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.ChildState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyChildState
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

lemma canonicalState_width (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    (canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ):=rfl

lemma canonicalState_power (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    Z^(canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      (τ.modulus.absNorm:ℝ)*dyadicScale (n 1):=by
  rw [canonicalState_width,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  ring

end SevenEighths.CenteredMomentEnergyChildState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalRadial
open HeckeFamily HeckeDyadic ConcreteTraceCRT MeasureTheory
open CenteredMomentAllocatedNaturalSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O

lemma naturalCharacter_eq (η : Character) (z : O) (hz : z≠0) :
    naturalCharacter η z=(naturalRow η z hz).character := by simp [naturalCharacter,hz]

variable {α : Type*} [Fintype α] [DecidableEq α]

end SevenEighths.CenteredMomentAllocatedNaturalRadial

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.instFiniteQuotientOIdeal_solutions
lemma relativeCharacter_fixedQ (η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q : Ideal O) (hQM : Q≤M) (hQη : Q≤η₀.modulus) :
    Q≤(relativeCharacter M H hH η₀ θ).modulus := le_inf hQM hQη

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma excluded_one_ideal (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

variable {M : Ideal O} [NeZero M]
variable {H : Subgroup (O⧸M)ˣ} (hH : RayOrthogonality.globalUnits M≤H)
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dirichlet
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

variable [NeZero q]

end SevenEighths.HeckeDirichlet

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P t : ℝ) :
    naturalSlot F.character pool (heightCoefficient β t) P=
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal]
  simp only [heightCoefficient,one_mul]
  ring

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.AllocatedChildren
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentDetectorDictionary CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma natural_product_eq_positive {η:Character}{z:O}(F:NaturalRow η z)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    polynomial F.character false W₁ X₁ 0 0*polynomial F.character false W₂ X₂ 0 0*
      ∏i,naturalSlot F.character (pool i) (β i) (P i)=
      CenteredMomentRetainedEnergy.positiveSlotRow η
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 z
        W₁ W₂ pool β P 0 X₁ X₂:=by
  rw [natural_unit_mask_positive F]
  have hh:=positiveSlotRow_eq_product η F.character fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W₁ W₂ pool β P X₁ X₂ 0 0 hX₁ hX₂ hP
  rw [twistProfile_zero,twistProfile_zero] at hh
  rw [hh]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hs:=CenteredMomentRayMaskedFloor.natural_slot_eq F (pool i) (β i) (P i) 0
  have he:heightCoefficient (β i) 0=β i:=by
    funext I
    simp only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  rw [he] at hs
  exact hs

lemma natural_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂ pool β P
      X₁ X₂ r.keep r.profile r.scale:=by
  unfold radialEnergy CenteredMomentInductionEnergy.energy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z
  · simp only [if_pos hk,naturalCharacter_eq η z (hz z hk)]
    rw [natural_product_eq_positive (naturalRow η z (hz z hk)) W₁ W₂ pool β P X₁ X₂ hX₁ hX₂ hP]
  · simp only [if_neg hk]

omit [Fintype α] in
lemma natural_subset_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (F:Finset α)(W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ r.keep r.profile r.scale:=by
  have hh:=natural_radial_eq_energy (α:=F) η r hz W₁ W₂
    (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ hX₁ hX₂
    (fun i=>hP i i.property)
  have hp (z:O):(∏i:F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))=
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i):=
    Finset.prod_coe_sort F (fun i:α=>naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
  simp_rw [hp] at hh
  exact hh

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum

lemma child_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α)
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>child (α:=α) (naturalCharacter η z) D a V₁ V₂ pool β P
      t X₁ X₂ hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale=
      allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J:=by
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  exact natural_subset_radial_eq_energy η r hz (liveIndices D a\J)
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    pool (fun i=>heightCoefficient (β i) t) P
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂) (fun i _=>hP i)

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CapacityRemoval
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCapacityRemoval
open HeckeFamily ConcreteTraceCRT CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot
open CenteredMomentSlotNormalization
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredExceptionalProfile CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCapacityRemoval.instFiniteQuotientOIdeal
theorem actual_relative_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀η₀:Character,∀θ:ι→RayQuotient.Characters M H,
    let ν:=fun i=>relativeCharacter M H hH η₀ (θ i);
    ∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=internalQ Q η₀ → Q≤M →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_state_capacity_removal M H hH W a b ha hWs hW
    Mrow bΦ Lmod Lslot ε lo hi κ hbΦ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀ θ
  dsimp only
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun i=>relativeCharacter M H hH η₀ (θ i))
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM
  exact henergy Z hZ Bmask s hpuncture hrow q hmod hLmod (internalQ Q η₀) hQ
    (inf_le_left.trans hQM)
    (fun i=>relativeCharacter_fixedQ M H hH η₀ (θ i) (internalQ Q η₀)
      (inf_le_left.trans hQM) inf_le_right)

end SevenEighths.CenteredMomentEnergyCapacityRemoval

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PaidBands
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPaidBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentPrimeSlot CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPaidBands.instFiniteQuotientOIdeal
omit [Fintype α] in
lemma remaining_energy_bound
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ)
    (hC₀:0≤C₀)(hC₁:0≤C₁)
    (hzero:ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C₁)
    (J R:Finset α)(θ:α→RayQuotient.Characters M H)(w σ v:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤w i)(hwL:∀i,w i≤Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤hi)
    (hheight:0≤height)(hv:∀i,|v i|≤height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤Mcap)
    (p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hcapacity:R=J ∨ length Z X₁+length Z X₂+6*κ*(∑i∈J\R,w i)≤ s.width):
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:↥(J\R)=>primePool M H bslot (Z^(w i)))
      (fun (i:↥(J\R)) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:↥(J\R)=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε) := by
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=sq_nonneg (p.control S)
  have hz:0≤Z^(s.width+ε):=Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _
  rcases hcapacity with hR|hcap
  · subst R
    let : IsEmpty ↥(J\J) := ⟨fun i=>by
      have hi:=Finset.mem_sdiff.mp i.property
      exact hi.2 hi.1⟩
    have he:=hzero s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hid : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i:↥(J\J)=>primePool M H bslot (Z^(w i)))
        (fun (i:↥(J\J)) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i:↥(J\J)=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
        s.plainEnergy p t X₁ X₂ := by
      simp only [energy,positiveSlotRow,NaturalState.plainEnergy,
        Fintype.prod_empty,mul_one]
    rw [hid]
    apply he.trans
    simp only [Real.norm_eq_abs]
    have hpow:(1+|t|)^degree≤(1+|t|+height)^degree :=
      pow_le_pow_left₀ (by positivity) (by linarith) degree
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₁) hd) hp)
      hpow (by positivity) (mul_nonneg (mul_nonneg (add_nonneg hC₀ hC₁) hd) hp)) hz
  · have he:=hpositive (J\R) (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>v i)
      t height (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
      hheight (fun i=>hv i) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
      (by simpa only [Finset.sum_coe_sort] using hcap)
    apply he.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀) hd) hp)
        (pow_nonneg (by positivity) _)) hz

end SevenEighths.CenteredMomentEnergyPaidBands

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.PaidRemoval
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyPaidRemoval
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidBands CenteredMomentEnergyCapacityRemoval
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyPaidRemoval.instFiniteQuotientOIdeal
theorem actual_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(J:Finset α)(w σ v:α→ℝ)(t height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|v i|≤height) →
    ∀s:NaturalState Z Bmask bΦ,s.puncture=1 → s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:J=>primePool M H bslot (Z^(w i)))
      (fun (i:J) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:J=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^(dc+degree)*
        Z^(s.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess J w (length Z X₁) (length Z X₂) s.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hrem⟩:=actual_relative_state_capacity_removal (ι:=α) M H hH
    (fun _=>W) (fun _=>aslot) (fun _=>bslot) (fun _=>ha) (fun _=>hWs) (fun _=>hW)
    Mcap bΦ (2*Mcap+1) Lslot εremove lo hi κ hbΦ (by linarith) hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hrem⟩:=hrem η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    J w σ v t height mesh hmesh hw hwm hwL hσlo hσhi hheight hv s hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hrem J w (length Z X₁) (length Z X₂)
    s.width mesh hmesh hw hwm hwL
  have hrow:s.rowWidth≤Mcap:=by
    have hc:=s.character_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have hq:Mcap+s.characterWidth+1≤2*Mcap+1:=by
    have hr:=s.row_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have he:=henergy Z hZ Bmask s hunit hrow s.characterWidth s.modulus_bound hq Q hQ hQM
    σ v t height hσlo hσhi hheight hv (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
  dsimp only at he
  have hb:=remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap εchild κ Z
    η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height
    hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  apply he.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_)
  simp only [pow_add,Real.rpow_add hZp]
  ring

end SevenEighths.CenteredMomentEnergyPaidRemoval

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.SlotHeight
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergySlotHeight
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentCommonMaskEnergy
open HeckePrimeAnnular CenteredMomentPrimeSlotShift
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α]

lemma height_coefficient (ν:Ideal O→ℂ)(W:ℝ→ℂ)(P σ freq t:ℝ)(hP:0<P)
    (I:Ideal O)(hI:I≠0):
    heightCoefficient (fun J=>ν J*annularWeight W P σ freq J) t I=
      (P:ℂ)^(Complex.I*t)*(ν I*annularWeight W P σ (t+freq) I):=by
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh:=norm_height_split (I.absNorm:ℝ) P σ t freq hN hP
  unfold heightCoefficient annularWeight
  calc
    _=(ν I*W ((I.absNorm:ℝ)/P))*
      (((((I.absNorm:ℝ)/P:ℝ):ℂ)^(-HeckeDyadic.shift σ freq))*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [show (I.absNorm:ℂ)=((I.absNorm:ℝ):ℂ) by simp,hh];ring

lemma row_slot_phase (η:Character)(m A z:O)(pool:Finset (Ideal O))
    (β γ:Ideal O→ℂ)(phase:ℂ)(t:ℝ)(he:∀I∈pool,β I=phase*γ I):
    rowSlot η m A z pool β t=phase*rowSlot η m A z pool γ t:=by
  unfold rowSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [he I hI]
  ring

lemma positive_row_phase (η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(he:∀i I,I∈pool i→β i I=phase i*γ i I):
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      (∏i,phase i)*positiveSlotRow η m A z W₁ W₂ pool γ P t X₁ X₂:=by
  have hs (i:α):rowSlot η m A z (pool i) (β i) t=
      phase i*rowSlot η m A z (pool i) (γ i) t:=
    row_slot_phase η m A z (pool i) (β i) (γ i) (phase i) t (he i)
  unfold positiveSlotRow
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  ring

theorem energy_phase (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (he:∀i I,I∈pool i→β i I=phase i*γ i I)(hp:∀i,‖phase i‖=1):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool γ P X₁ X₂ keep Φ K:=by
  have hprod:‖∏i,phase i‖=1:=by rw [norm_prod];simp only [hp,Finset.prod_const_one]
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row_phase η m A z W₁ W₂ pool β γ phase P t X₁ X₂ he]
  simp only [norm_mul,hprod,one_mul]

theorem inherited_height_energy (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(ν:α→Ideal O→ℂ)(W:α→ℝ→ℂ)
    (P σ freq:α→ℝ)(hP:∀i,0<P i)(hpool:∀i I,I∈pool i→I≠0)
    (t rowt X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A rowt W₁ W₂ pool
      (fun i=>heightCoefficient (fun I=>ν i I*annularWeight (W i) (P i) (σ i) (freq i) I) t)
      P X₁ X₂ keep Φ K=
    energy η m A rowt W₁ W₂ pool
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+freq i) I)
      P X₁ X₂ keep Φ K:=by
  apply energy_phase η m A W₁ W₂ pool _ _ (fun i=>(P i:ℂ)^(Complex.I*t)) P rowt X₁ X₂ keep Φ K
  · intro i I hi
    exact height_coefficient (ν i) (W i) (P i) (σ i) (freq i) t (hP i) I (hpool i I hi)
  · intro i
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (hP i) (Complex.I*t)

end SevenEighths.CenteredMomentEnergySlotHeight

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.Reindex
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyReindex
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

variable {α β:Type*}[Fintype α][Fintype β]

lemma positive_reindex (e:α≃β)(η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ (pool∘e) (coeff∘e) (P∘e) t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ pool coeff P t X₁ X₂:=by
  unfold positiveSlotRow
  simp only [Function.comp_apply,e.prod_comp P,
    e.prod_comp (fun i=>CenteredMomentHeckeSlots.rowSlot η m A z (pool i) (coeff i) t)]

theorem energy_reindex (e:α≃β)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (pool∘e) (coeff∘e) (P∘e) X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool coeff P X₁ X₂ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_reindex]

omit [Fintype α] [Fintype β] in
theorem energy_subset_map (e:α↪β)(T:Finset α)(η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:β→Finset (Ideal O))(coeff:β→Ideal O→ℂ)(P:β→ℝ)(t X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ (fun i:T=>pool (e i)) (fun i:T=>coeff (e i))
      (fun i:T=>P (e i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i)
      (fun i:T.map e=>P i) X₁ X₂ keep Φ K:=
  energy_reindex (Finset.equivMap e T) η m A W₁ W₂
    (fun i:T.map e=>pool i) (fun i:T.map e=>coeff i) (fun i:T.map e=>P i)
    t X₁ X₂ keep Φ K

end SevenEighths.CenteredMomentEnergyReindex

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]

section RayData
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

variable {M H hH}
variable {s : Input α} {η₀ : Character} {θ : α → RayQuotient.Characters M H}
  {w σ freq : α → ℝ} {W : ℝ → ℂ} {bslot Z : ℝ}
  (h : Matches M H hH s η₀ θ w σ freq W bslot Z)

include h

attribute [local instance] OAI.SevenEighths.CenteredMomentAllocatedRayDictionary.instFiniteQuotientOIdeal_solutions
omit [DecidableEq α] in
lemma common_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I =
      idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I := by
  change s.ν i.val I * s.W i.val ((I.absNorm : ℝ) / s.P i.val) = _
  rw [h.character, h.profile, h.scale]
  rfl

theorem common_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (m A : O) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    energy τ m A 0 W₁ W₂
      (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) X₁ X₂ keep Φ K =
    energy τ m A 0 W₁ W₂
      (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) X₁ X₂ keep Φ K := by
  dsimp only
  have hc : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).coefficient i.val) =
      fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val.val)) I *
        annularWeight W (Z^(w i.val.val)) (σ i.val.val) (freq i.val.val) I := by
    funext i I
    exact common_coefficient h τ v C R B i.val I
  have hp : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).P i.val) = fun i => Z^(w i.val.val) := by
    funext i
    exact h.scale i.val.val
  have hs : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).slots i.val) =
      fun i => primePool M H bslot (Z^(w i.val.val)) := by
    funext i
    exact h.pool i.val.val
  have hhc := congrArg (fun f => fun i : remaining s C B L a J => heightCoefficient (f i) v) hc
  rw [hhc, hp, hs]
  rw [CenteredMomentEnergySlotHeight.inherited_height_energy τ m A W₁ W₂ _ _ _ _ _ _
    (fun i => h.scale i.val.val ▸ s.P_pos i.val.val)
    (fun i I hI => (s.prime i.val.val I (by rw [h.pool]; exact hI)).ne_zero)
    v 0 X₁ X₂ keep Φ K]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (remaining s C B L a J) τ m A W₁ W₂
    (fun i => primePool M H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
    (fun i => Z^(w i)) 0 X₁ X₂ keep Φ K

omit h

end RayData
end SevenEighths.CenteredMomentAllocatedRayDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.AllocatedPaid
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedPaid
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidRemoval CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid.instFiniteQuotientOIdeal
theorem actual_allocated_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    let d:=commonData (withHeight src st.character v) C R B
    energy st.character st.mask 1 0 (p.profile 0) (p.profile 1)
      (fun i:remaining src C B D alloc J=>d.slots i.val)
      (fun i:remaining src C B D alloc J=>CenteredMomentCommonMaskEnergy.heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining src C B D alloc J=>d.P i.val)
      X₁ X₂ st.radial.keep st.radial.profile st.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*(p.control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z X₁) (length Z X₂) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  rw [common_energy hmatch st.character v C R B D alloc J st.mask 1
    (p.profile 0) (p.profile 1) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale]
  have he:=hbound Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    (originalImage src C B D alloc J) w σ (fun i=>v+freq i) 0 (|v|+height) mesh
    hmesh hw hwm hwL hσlo hσhi (add_nonneg (abs_nonneg _) hheight)
    (fun i=>(abs_add_le _ _).trans (add_le_add le_rfl (hfreq i)))
    st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [abs_zero,add_zero] using he

end SevenEighths.CenteredMomentEnergyAllocatedPaid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalStability
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open CenteredMomentRetainedProfile CenteredMomentAllocatedNaturalSource
open EisensteinSchwartzPoisson CenteredMomentLattice

theorem plain_profile_source_control (a b:ℝ) (ha:0<a) (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      ∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀U:ℝ,∀hU:0<U,∀t:ℝ,
      sourceControl S ((sourcePlain a b ha W hs).profile U hU t)≤
        C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hsource⟩ := normPowerProfile_source_control a b ha S
  refine ⟨n,T,(max 1 b)^(S.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs U hU t
  have hp:=sourceControl_nonneg T W
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    have hd:=normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation U)
      ha (le_max_left _ _) (clipDilation_ge_one U hU) (clipDilation_le b U hU hret)
      hs (W.smooth ⊤) t S
    exact hd.trans ((mul_le_mul_of_nonneg_left (hsource W hs t) (by positivity)).trans_eq (by dsimp only [sourceControl]; ring))
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simpa only [sourceControl,map_zero] using
      (show 0≤(max 1 b)^(S.sup Prod.snd)*C*sourceControl T W*(1+‖t‖)^n by positivity)

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.AllocatedProfiles
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedProfiles
open CenteredMomentFiniteProfileExceptional

theorem retained_pair_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀p:Profiles a b,∀U:Fin 2→ℝ,∀hU:∀i,0<U i,∀t:ℝ,
      (retainedPair a b ha p U hU t).control S≤
        C*p.control T*(1+‖t‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hbound⟩:=plain_profile_source_control a b ha S
  refine ⟨n,T,C ^2,sq_pos_of_pos hC,?_⟩
  intro p U hU t
  have h₀:=hbound (p.profile 0) (p.support 0) (U 0) (hU 0) t
  have h₁:=hbound (p.profile 1) (p.support 1) (U 1) (hU 1) t
  have hp₀:=sourceControl_nonneg T (p.profile 0)
  change sourceControl S _*sourceControl S _≤_
  apply (mul_le_mul h₀ h₁ (sourceControl_nonneg _ _) (by positivity)).trans_eq
  simp only [Profiles.control,show 2*n=n+n by omega,pow_add]
  ring

end SevenEighths.CenteredMomentEnergyAllocatedProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.AllocatedZero
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedZero
open HeckeFamily CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAllocatedNaturalSource CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma allocatedScale_le (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(X:ℝ)(hX:0<X)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):
    clippedScale (rawScale D a X j)/(Ideal.absNorm (∏I∈F,I):ℝ)≤ max 1 X:=by
  have hn:1≤(Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a j):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hf:1≤(Ideal.absNorm (∏I∈F,I):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr hF))
  have hx:rawScale D a X j≤X:=div_le_self hX.le hn
  exact (div_le_self (by unfold clippedScale;positivity) hf).trans
    (max_le_max_left 1 hx)

end SevenEighths.CenteredMomentEnergyAllocatedZero

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.AllocatedClipped
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

lemma scale_pos (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):0<scale D alloc X j F:=by
  have hn:0<((∏I∈F,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hF))
  exact div_pos (by unfold clippedScale;positivity) hn

lemma scale_cap (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (Z L X:ℝ)(hZ:1≤Z)(hL:0≤L)(hX:0<X)(hc:X≤Z^L)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):scale D alloc X j F≤Z^L:=
  (allocatedScale_le D alloc X hX j F hF).trans (max_le (Real.one_le_rpow hZ hL) hc)

lemma allocated_pair {Z Bmask bΦ a b:ℝ}(st:NaturalState Z Bmask bΦ)(hunit:st.puncture=1)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (ha:0<a)(p:Profiles a b)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1)) pool β P v X₁ X₂ hX₁ hX₂ F₁ F₂ J =
    energy st.character st.mask 1 0
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 0)
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 1)
      (fun i:↥(liveIndices D alloc\J)=>pool i)
      (fun i:↥(liveIndices D alloc\J)=>CenteredMomentCommonMaskEnergy.heightCoefficient (β i) v)
      (fun i:↥(liveIndices D alloc\J)=>P i)
      (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
      st.radial.keep st.radial.profile st.radial.scale:=by
  simp only [allocatedEnergy,pair,retainedPair,scale,NaturalState.mask,hunit,
    Matrix.cons_val_zero,Matrix.cons_val_one]

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped.instFiniteQuotientOIdeal_solutions
theorem actual_clipped_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(ha:0<a),0≤L → ∀Q:Ideal O,Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_allocated_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild ha hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  rw [allocated_pair st hunit]
  exact hbound Z hZ (a/max 1 b) b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs (pair D alloc ha p v X₁ X₂ hX₁ hX₂)
    (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
    (scale_pos D alloc X₁ 0 F₁ hF₁) (scale_pos D alloc X₂ 1 F₂ hF₂)
    (scale_cap D alloc Z L X₁ st.base_ge_one hL hX₁ hc₁ 0 F₁ hF₁)
    (scale_cap D alloc Z L X₂ st.base_ge_one hL hX₂ hc₂ 1 F₂ hF₂)

end SevenEighths.CenteredMomentEnergyAllocatedClipped

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.AllocatedHomogeneous
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous.instFiniteQuotientOIdeal
theorem actual_clipped_homogeneous_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(Bmask εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_clipped_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  obtain ⟨n,T,Cp,hCp,hprofile⟩:=retained_pair_control a b haPlain S
  refine ⟨n,T,dc,Cc*Cp^2,mul_pos hCc (sq_pos_of_pos hCp),?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ Bmask εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have he:=hbound Z hZ a b Bmask L εchild haPlain hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only at he ⊢
  let U:Fin 2→ℝ:=![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
  have hU:∀i,0<U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D alloc X₁ hX₁ 0
    · exact rawScale_pos D alloc X₂ hX₂ 1
  have hp:(pair D alloc haPlain p v X₁ X₂ hX₁ hX₂).control S≤
      Cp*p.control T*(1+|v|+height)^(2*n):=by
    have h:=hprofile p U hU v
    have hpw:(1+‖v‖)^(2*n)≤(1+|v|+height)^(2*n):=
      pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith) _
    exact h.trans (mul_le_mul_of_nonneg_left hpw (mul_nonneg hCp.le (p.control_nonneg T)))
  apply he.trans
  calc
    _≤Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (Cp*p.control T*(1+|v|+height)^(2*n))^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans st.base_ge_one) _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2)
        (mul_nonneg (mul_nonneg hCc.le (add_nonneg hC₀ hC₁)) (diagonalControl_nonneg _))
    _=_:=by
      have hpow:(1+|v|+height)^(4*n)=((1+|v|+height)^(2*n))^2:=by
        rw [←pow_mul]
        congr 1
        omega
      simp only [←add_assoc,mul_pow,pow_add,hpow]
      ring

end SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalChildBound
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalChildBound
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound.instFiniteQuotientOIdeal
theorem actual_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        ((τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1))*
        Z^(εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) (Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_clipped_homogeneous_bands (α:=α) M H hH W aslot bslot
    Mcap 2 Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap (by norm_num)
    hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hZ1:1<Z:=hZ₀.trans_le hZ
  let st:=canonicalState Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  have he:=hbound Z hZ 0 εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st rfl rfl hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hpow:=canonicalState_power Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  change Z^st.width=(τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1) at hpow
  dsimp only at he ⊢
  have heq:st.width+εchild+εremove+
      CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
        (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh =
    st.width+(εchild+εremove+CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by ring
  rw [heq,Real.rpow_add (zero_lt_one.trans hZ1),hpow] at he
  convert (preTransparency := .instances) he using 1 <;> simp only [st,canonicalState,NaturalState.width] ; ring

end SevenEighths.CenteredMomentEnergyCanonicalChildBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CanonicalLiveBound
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLiveBound
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem energy_zero_of_not_live (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α)
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hn:¬LiveChild η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
  rw [←child_radial_eq_energy η r hz D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂]
  unfold radialEnergy
  apply (tsum_congr (g:=fun _ : O=>(0:ℝ)) ?_).trans (tsum_zero)
  intro z
  by_cases hk:r.keep z
  · rw [if_pos hk]
    by_cases hφ:(r.profile (‖eisEmbedding z‖^2/r.scale)).re=0
    · rw [hφ,mul_zero]
    · have hc:child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
        by_contra hh
        exact hn ⟨z,hk,hφ,hh⟩
      simp only [hc,norm_zero,zero_pow (by decide:2≠0),zero_mul]
  · rw [if_neg hk]

open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound.instFiniteQuotientOIdeal_solutions
theorem actual_live_canonical_child_bands_oai (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀Mnom cost:ℝ,
    (LiveChild τ (canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J →
      Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom+
        CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
          (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂))
          (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6≤ cost) →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+cost+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro Mnom cost hcost
  have hz:1<Z:=hZ₀.trans_le hZ
  have hz0:0<Z:=zero_lt_one.trans hz
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  by_cases hne:LiveChild τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J
  · have he:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    dsimp only at he
    have hnorm:0<(τ.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
    have hpower:Z^(Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))=
        (τ.modulus.absNorm:ℝ)*dyadicScale (dyad 1):=by
      rw [Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' (dyadicScale_pos _),
        Real.rpow_logb hz0 hz.ne' hnorm,mul_comm]
    apply he.trans
    rw [←hpower,mul_assoc,←Real.rpow_add hz0]
    apply mul_le_mul_of_nonneg_left _ (by
      have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
      have hp:=p.control_nonneg T
      positivity)
    apply Real.rpow_le_rpow_of_exponent_le hz.le
    have hh:=hcost hne
    linarith
  · have he:=energy_zero_of_not_live τ rad (fun z hz=>hz.1) D alloc V₁ V₂
      d.slots d.coefficient d.P d.P_pos v X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂ hne
    change allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J≤_
    rw [he]
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hp:=p.control_nonneg T
    positivity

end SevenEighths.CenteredMomentEnergyCanonicalLiveBound

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound.actual_live_canonical_child_bands_oai.{u_1} := @OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound.actual_live_canonical_child_bands_oai.{u_1}
