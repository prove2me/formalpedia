-- Prove2me | solution 1 for OAI.SevenEighths.DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:00:34.371901+00:00
-- url     : https://prove2.me/submissions/6858ea15-035c-41e1-9206-9adb0d465e40

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

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
namespace CubicReflectionKernel

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

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

lemma logPhase_add_frequency (t s x : ℝ) :
    logPhase (t + s) x = logPhase t x * logPhase s x := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma frequencyTwist_twice (g : 𝓢(ℝ, ℂ)) (t s : ℝ) :
    frequencyTwist (frequencyTwist g t) s = frequencyTwist g (t + s) := by
  ext x
  simp only [frequencyTwist_apply, logPhase_add_frequency]
  ring

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DescentProfiles
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert (preTransparency := .instances) schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapFourier
open InverseMoment
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem density_norm (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ‖density g xj t‖=‖(𝓕 g) t‖ := by
  simp only [density,norm_mul,logPhase_norm,mul_one]

lemma fourier_phase_integrable (g : 𝓢(ℝ,ℂ)) (x : ℝ) (a : ℂ) :
    Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x*a) := by
  have h : Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x) (volume:Measure ℝ) :=
    (𝓕 g).integrable.mul_bdd (c:=1)
    (logPhase_continuous_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>le_of_eq (logPhase_norm t x)))
  exact h.mul_const a

end SevenEighths.InverseInitialOverlapFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ClippedFourier
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier SecondPassIntegration JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem clipped_test_fourier (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ y:ℝ)(hc:0<c)(hy:0<y)(hwFresh:wFresh y*W (c*y)=W (c*y)):
    clippedTest W c θ y =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        childLogTest wFresh (θ+t) y:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  change clippedTest W c θ y=∫t:ℝ,density g (Real.log c) t*childLogTest wFresh (θ+t) y
  have he (t:ℝ):density g (Real.log c) t*childLogTest wFresh (θ+t) y=
      ((𝓕 g) t*logPhase t (Real.log c+Real.log y))*(wFresh y*logPhase θ (Real.log y)):=by
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hi':(∫t:ℝ,(𝓕 g) t*logPhase t (Real.log c+Real.log y))=W (c*y):=by
    calc
      _=(∫t:ℝ,logPhase t (Real.log c+Real.log y)*(𝓕 g) t):=by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _=g (Real.log c+Real.log y):=(schwartz_logPhase_inversion g _).symm
      _= _:=by
        simp only [g,CubicReflectionKernel.logSchwartz_apply,Real.exp_add,Real.exp_log hc,Real.exp_log hy]
  rw [hi']
  unfold clippedTest childLogTest
  calc
    W (c*y)*logPhase θ (Real.log y)=(wFresh y*W (c*y))*logPhase θ (Real.log y):=by rw [hwFresh]
    _= _:=by ring

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem finite_weighted_integral_energy {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (w : ℝ → ℝ) (hw : ∀ t,0<w t)
    (E : ℝ) (hE : 0≤E) (hb : Integrable (fun t => w t*‖b t‖))
    (hφ : ∀ k,Integrable (fun t => b t*φ k t))
    (hbound : ∀ t,(∑ k,‖φ k t‖^2)≤E*(w t)^2) :
    (∑ k,‖∫ t : ℝ,b t*φ k t‖^2)≤E*(∫ t : ℝ,w t*‖b t‖)^2 := by
  have hn (t : ℝ) : (w t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw t).ne'
  have hnorm (t : ℝ) : ‖(w t:ℂ)‖=w t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw t)]
  have he (k : κ) (t : ℝ) : ((w t:ℂ)*b t)*(φ k t/(w t:ℂ))=b t*φ k t := by
    field_simp [hn t]
  have hh := CompletedGauss.finite_integral_energy_bound
    (fun t => (w t:ℂ)*b t) (fun k t => φ k t/(w t:ℂ)) E hE
    (by simpa only [norm_mul,hnorm] using hb)
    (fun k => by simpa only [he] using hφ k) (fun t => by
      simp only [norm_div,hnorm,div_pow,← Finset.sum_div]
      exact (div_le_iff₀ (sq_pos_of_pos (hw t))).mpr (hbound t))
  simpa only [he,norm_mul,hnorm] using hh

end SevenEighths.CenteredMomentHeckeWindowEnergy

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicProfiles
namespace OAI

noncomputable section

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open CubicReflectionKernel
theorem section_deriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : (ℝ × ℝ) × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

lemma inverseProfile_eq_ratio (V W : ℝ→ℂ) (Dstar D : ℝ) :
    HeckeDetectorDyadicBridge.inverseProfile V W Dstar D=ratioProfile V W (D/Dstar) := by
  funext x
  unfold HeckeDetectorDyadicBridge.inverseProfile ratioProfile
  congr 2
  ring

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicCutoff
namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open HeckeDetectorProfiles

lemma positiveAnnular_eq (x : ℝ) (hx : 0≤x) :
    positiveAnnular x=DyadicTransfer.annularCutoff cutoff x :=
  (Classical.choose_spec exists_positive_annular).2.2 x hx

end SevenEighths.HeckeDetectorDyadicProfiles

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeDetectorDyadicProfiles

theorem compact_family_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀p∈J,SchwartzMap.seminorm ℝ k n (G p)≤C := by
  have hc := (section_iteratedDeriv_smooth F hF n).continuous.norm
  obtain ⟨M,hM⟩ := (hJ.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨1+L^k*(|M|+1),by positivity,?_⟩
  intro p hp
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro x
  have he : (G p : ℝ→ℂ)=F p := funext (hG p)
  rw [he]
  by_cases hx : x∈Icc (-L) L
  · have hnorm : ‖iteratedDeriv n (F p) x‖≤|M|+1 := by
      have hb := hM (Set.mem_image_of_mem _ (show (p,x)∈J×ˢIcc (-L) L from ⟨hp,hx⟩))
      exact hb.trans (by linarith [le_abs_self M])
    have hxp : ‖x‖^k≤L^k := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using hx
    exact (mul_le_mul hxp hnorm (norm_nonneg _) (pow_nonneg hL k)).trans (by linarith)
  · have hout : iteratedDeriv n (F p) x=0 := by
      by_contra hn
      have hx' := (subset_tsupport (iteratedDeriv n (F p))) hn
      have hh := (CubicReflectionKernel.tsupport_iteratedDeriv_subset (F p) n) hx'
      exact hx ((closure_minimal (hs p) isClosed_Icc) hh)
    rw [hout,norm_zero,mul_zero]
    positivity

theorem compact_family_finite_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀p∈J,S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G p)≤C := by
  choose C hC hb using fun z : ℕ×ℕ=>compact_family_seminorm F hF L hL hs J hJ G hG z.1 z.2
  have hsum : 0≤∑z∈S,C z := Finset.sum_nonneg (fun z _=>(hC z).le)
  refine ⟨1+∑z∈S,C z,by linarith,?_⟩
  intro p hp
  apply Seminorm.finset_sup_apply_le (by linarith)
  intro z hz
  apply (hb z p hp).trans
  have hh := Finset.single_le_sum (fun z (_ : z∈S)=>(hC z).le) hz
  linarith

theorem compact_family_frequencyTwist
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀p∈J,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (JointLogSeparation.frequencyTwist (G p) t)≤C*(1+‖t‖)^n := by
  let S' := S.biUnion (fun z=> (Finset.range (z.2+1)).image (fun i=>(z.1,i)))
  obtain ⟨B,hB,hbound⟩ := compact_family_finite_seminorm F hF L hL hs J hJ G hG S'
  let c : ℕ×ℕ→ℝ := fun z=>(2:ℝ)^z.2*(1+2*Real.pi)^z.2*((z.2+1)*B)
  have hc (z : ℕ×ℕ) : 0≤ c z := by dsimp [c];positivity
  have hsum : 0≤∑z∈S,c z := Finset.sum_nonneg (fun z _=>hc z)
  refine ⟨S.sup Prod.snd,1+∑z∈S,c z,by linarith,?_⟩
  intro p hp t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hd : JointLogSeparation.derivativeSeminormSum (G p) z.1 z.2≤(z.2+1)*B := by
    unfold JointLogSeparation.derivativeSeminormSum
    calc
      _≤∑i∈Finset.range (z.2+1),B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : (z.1,i)∈S' := Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
        exact (Seminorm.le_finset_sup_apply hi').trans (hbound p hp)
      _=_ := by simp
  have hzC : c z≤1+∑z∈S,c z := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S)=>hc z) hz
    linarith
  have he := JointLogSeparation.frequencyTwist_seminorm_polynomial (G p) t z.1 z.2
  have hb : SchwartzMap.seminorm ℝ z.1 z.2 (JointLogSeparation.frequencyTwist (G p) t)≤ c z*(1+‖t‖)^z.2 := by
    apply he.trans
    dsimp only [c]
    gcongr
  exact hb.trans (mul_le_mul hzC
    (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)) (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformLog
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic

lemma realInterpolatedLog_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (realInterpolatedLog W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hw : W (Real.exp x)≠0 := by intro hw;exact hx (by simp [realInterpolatedLog,hw])
  have hlo : Real.log a≤x := by simpa only [Real.log_exp] using Real.log_le_log ha (hs hw).1
  have hhi : x≤Real.log b := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) (hs hw).2
  constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),abs_nonneg (Real.log a),abs_nonneg (Real.log b)]

lemma realInterpolatedLogSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) (x : ℝ) :
    realInterpolatedLogSchwartz W a b ha hs hW p x=realInterpolatedLog W p x := by
  rw [realInterpolatedLogSchwartz,CubicReflectionKernel.logSchwartz_apply]
  unfold twistProfile realInterpolatedLog
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ←Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero]
  change W (Real.exp x)*Complex.exp ((x:ℂ)*-(p.1:ℂ))=
    ((Real.exp (-p.1*x):ℝ):ℂ)*W (Real.exp x)
  rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  have he : (x:ℂ)*-(p.1:ℂ)=-(p.1:ℂ)*(x:ℂ) := by ring
  rw [he,mul_comm]

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseUniformLog
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial CenteredMomentDetectorDictionary

lemma logTest_apply (W : ℝ→ℂ) (n : ℕ) (x : ℝ) :
    logTest W n x=(Real.log x:ℂ)^n*W x := by
  induction n with
  | zero => simp [logTest]
  | succ n ih => simp only [logTest,logProfile,ih,pow_succ];ring

lemma inverseLogFamily_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (inverseLogFamily reverse n V W)) := by
  have hv : ContDiff ℝ ∞ (orientedProfile reverse V) := by
    cases reverse
    · exact hV
    · exact conjugate_profile_smooth _ hV
  have hw : ContDiff ℝ ∞ (orientedProfile reverse W) := by
    cases reverse
    · exact hW
    · exact conjugate_profile_smooth _ hW
  unfold inverseLogFamily Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>Real.exp (-p.1.1*p.2))).smul
    (((Complex.ofRealCLM.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>p.2))).pow n).mul
      ((hv.comp (by fun_prop)).mul (hw.comp (by fun_prop))))

lemma inverseLogFamily_eq (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) :
    inverseLogFamily reverse n V W p x=realInterpolatedLog (baseProfile reverse n V W p.2) p x := by
  unfold inverseLogFamily realInterpolatedLog baseProfile
  rw [logTest_apply,Real.log_exp]
  cases reverse <;> simp [orientedProfile,ratioProfile,map_mul]

lemma inverseLogFamily_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (inverseLogFamily reverse n V W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  have he : inverseLogFamily reverse n V W p=realInterpolatedLog (baseProfile reverse n V W p.2) p :=
    funext (inverseLogFamily_eq reverse n V W p)
  rw [he]
  exact realInterpolatedLog_support _ a b ha ((baseProfile_support reverse n V W p.2).trans hs) p

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseUniformFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic JointLogSeparation CenteredMomentDetectorDictionary

lemma inverseLogSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) (x : ℝ) :
    inverseLogSchwartz reverse n V W a b ha hV hW hs p x=inverseLogFamily reverse n V W p x := by
  rw [inverseLogSchwartz,realInterpolatedLogSchwartz_apply,inverseLogFamily_eq]

theorem inverseSchwartz_operator_uniform (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) (Rmax : ℝ)
    (op : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀R∈Icc (0:ℝ) Rmax,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤C*(1+‖t‖)^J := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (op.comp (CompletedHeight.fixedLogReturnCLM a b ha)) S
  obtain ⟨J,B,hB,hbound⟩ := compact_family_frequencyTwist
    (inverseLogFamily reverse n V W) (inverseLogFamily_smooth reverse n V W hV hW)
    (|Real.log a|+|Real.log b|) (by positivity) (inverseLogFamily_support reverse n V W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax) (isCompact_Icc.prod isCompact_Icc)
    (inverseLogSchwartz reverse n V W a b ha hV hW hs)
    (inverseLogSchwartz_apply reverse n V W a b ha hV hW hs) T
  refine ⟨J,A*B,mul_pos hA hB,?_⟩
  intro R hR σ hσ t
  have hp : (σ,R)∈Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax := ⟨hσ,hR⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))≤B*(1+‖t‖)^J :=
    (hbound (σ,R) hp (t/(2*Real.pi))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) J) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseUniformTests
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

lemma inverseDetectorTest_apply (scaled reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorTest scaled reverse n R σ t x=
      if scaled then scaleProfile (twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t) x
      else twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x := by
  have he : (inverseDetectorSchwartz reverse n R σ t : ℝ→ℂ)=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t :=
    funext (inverseDetectorSchwartz_apply reverse n R σ t)
  cases scaled
  · exact inverseDetectorSchwartz_apply _ _ _ _ _ _
  · change scaleCLM (inverseDetectorSchwartz reverse n R σ t) x=_
    rw [scaleCLM_apply,he]
    rfl

theorem inverseDetectorTest_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R∈Icc (0:ℝ) 4,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Bool×Fin 3=>inverseSchwartz_operator_uniform
    q.2.1 q.2.2.val cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support 4 (sourceOperator q.1) S
  let J := (Finset.univ : Finset (Bool×Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Bool×Fin 3,C q,by linarith,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  let q : Bool×Bool×Fin 3 := (scaled,reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q R hR σ hσ t
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseUniformSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial

lemma positiveAnnular_support_sharp : Function.support positiveAnnular⊆Ioo (1/2) 2 := by
  intro x hx
  have hx0 : 0≤x := by have := (positiveAnnular_support hx).1; linarith
  have he : DyadicTransfer.annularCutoff cutoff x≠0 := by
    rwa [←positiveAnnular_eq x hx0]
  simpa using HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx0 0 (by simpa using he)

lemma ratioProfile_zero_of_four_le (R : ℝ) (hR : 4≤R) :
    ratioProfile cutoff positiveAnnular R=0 := by
  funext x
  by_cases hx : positiveAnnular x=0
  · simp [ratioProfile,hx]
  · have hs := positiveAnnular_support_sharp hx
    have hrx : 2≤R*x := by nlinarith [hs.1]
    simp [ratioProfile,cutoff_zero _ hrx]

lemma inverseDetectorTest_zero_of_four_le (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ)
    (hR : 4≤R) : inverseDetectorTest scaled reverse n R σ t=0 := by
  have hz : inverseDetectorSchwartz reverse n R σ t=0 := by
    ext x
    rw [inverseDetectorSchwartz_apply]
    simp only [baseProfile,ratioProfile_zero_of_four_le R hR]
    cases reverse <;> simp [orientedProfile,twistProfile,HeckeDyadic.shift,logTest_apply]
  rw [inverseDetectorTest,hz,map_zero]

theorem inverseDetectorTest_uniform_all_ratios (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R : ℝ,0≤R→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  by_cases hh : R≤4
  · exact hb scaled reverse n hn R ⟨hR,hh⟩ σ hσ t
  · rw [inverseDetectorTest_zero_of_four_le _ _ _ _ _ _ (le_of_not_ge hh),map_zero]
    positivity

lemma inverseSourceSchwartz_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    inverseSourceSchwartz scaled reverse n U tstar r σ t x=
      if scaled then scaleProfile (twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t) x
      else twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t x := by
  simp only [inverseSourceSchwartz,inverseDetectorTest_apply,baseProfile,
    HeckeDetectorInverseFiberCount.inverseTest,inverseProfile_eq_ratio]

theorem inverseSourceSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀U : ℝ,0<U→∀tstar r : ℝ,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseSourceSchwartz scaled reverse n U tstar r σ t)≤C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform_all_ratios S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t
  exact hb scaled reverse n hn (U^r/U^tstar) (by positivity) σ hσ t

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseClippedUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseUniform HeckeInverseAmplification
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem referenceWindow_support : tsupport (referenceWindow : ℝ→ℂ) ⊆
    Set.Icc (1/18 : ℝ) (13/4) :=
  (Classical.choose_spec exists_reference_window).2.1

theorem referenceWindow_one (x : ℝ) (hx : x∈Set.Icc (1/9 : ℝ) (9/4)) :
    referenceWindow x = 1 :=
  (Classical.choose_spec exists_reference_window).2.2 x hx

theorem referenceWindow_agrees (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c y : ℝ)
    (hc : 1≤ c) (hcb : c≤9/4) (hy : 0<y) :
    referenceWindow y * inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) := by
  by_cases hz : inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) = 0
  · simp [hz]
  have hs := source_support scaled reverse n U tstar r σ t hz
  have hh : y∈Set.Icc (1/9 : ℝ) (9/4) := by
    constructor <;> nlinarith [hs.1,hs.2]
  rw [referenceWindow_one y hh,one_mul]

theorem logSource_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    logSource scaled reverse n U tstar r σ t x =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (Real.exp x) :=
  CubicReflectionKernel.logPullbackCLM_eq_actual _ _ (by norm_num) _
    (source_support scaled reverse n U tstar r σ t) x

theorem logSource_eq_logSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    logSource scaled reverse n U tstar r σ t =
      CubicReflectionKernel.logSchwartz (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
        ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤) := by
  ext x
  rw [logSource_apply,CubicReflectionKernel.logSchwartz_apply]

theorem familyDensity_norm (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    ‖familyDensity scaled reverse n U tstar r σ t c v‖ =
      ‖(𝓕 (logSource scaled reverse n U tstar r σ t)) v‖ := density_norm _ _ _

theorem familyDensity_moment (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
      ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t c : ℝ,
      (∫v : ℝ, (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) ≤
        C*(1+‖t‖)^K := by
  let p := (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ×ℕ) := Finset.Iic (p,J+p)
  obtain ⟨T,A,hA,hop⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM (1/4) (9/4)) S
  obtain ⟨K,B,hB,hsource⟩ := inverseSourceSchwartz_uniform T
  let C := 1+(2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B))
  have hC : 0<C := by
    have h₀ := coefficientMomentBound_nonneg 0 (2*A*B) (by positivity)
    have hJ := coefficientMomentBound_nonneg J (2*A*B) (by positivity)
    dsimp [C]
    positivity
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t c
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  let g := logSource scaled reverse n U tstar r σ t
  have hb : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤ A*B*(1+‖t‖)^K := by
    exact (hop W).trans ((mul_le_mul_of_nonneg_left
      (hsource scaled reverse n hn U hU tstar r σ hσ t) hA.le).trans_eq (by ring))
  have hs (i : ℕ) (hi : i≤J+p) :
      (SchwartzMap.seminorm ℝ 0 i) g + (SchwartzMap.seminorm ℝ p i) g ≤
        2*A*B*(1+‖t‖)^K := by
    have h₀ : schwartzSeminormFamily ℝ ℝ ℂ (0,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have hp : schwartzSeminormFamily ℝ ℝ ℂ (p,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have h₁ := (Seminorm.le_def.mp h₀ g).trans hb
    have h₂ := (Seminorm.le_def.mp hp g).trans hb
    change (SchwartzMap.seminorm ℝ 0 i) g ≤ _ at h₁
    change (SchwartzMap.seminorm ℝ p i) g ≤ _ at h₂
    linarith
  have hmoment := uniform_fourier_one_plus_moment g J 1
    (2*A*B*(1+‖t‖)^K) (by norm_num) (by positivity)
    (by intro i hi; simpa only [one_mul] using hs i hi)
  simp only [one_mul] at hmoment
  simp only [familyDensity_norm]
  apply hmoment.trans
  have he : (2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B*(1+‖t‖)^K)+
      coefficientMomentBound J (2*A*B*(1+‖t‖)^K)) =
      ((2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B)))*(1+‖t‖)^K := by
    unfold coefficientMomentBound
    ring
  rw [he]
  dsimp [C]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end SevenEighths.DetectorDictionaryInverseClippedUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

end SevenEighths.InverseInitialRawDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawFourier
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge InverseInitialRawDictionary
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier FourierBridge JointLogSeparation

private theorem child_cover (Wref : ℝ→ℂ) (b D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) (s : ℝ) :
    ∀I : Ideal O,I≠0 → childLogTest Wref s ((I.absNorm:ℝ)/D)≠0 →
      I∈ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊ := by
  intro I hI hi
  apply finite_source_cover Wref D b hD hWref I hI
  intro hz
  exact hi (by simp [childLogTest,hz])

theorem polynomial_mode_integrable (χ : Character) (inv : Bool)
    (g : 𝓢(ℝ,ℂ)) (Wref : ℝ→ℂ) (b c θ D : ℝ) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b) :
    Integrable (fun v:ℝ=>density g (Real.log c) v*
      polynomial χ inv (childLogTest Wref (θ+v)) D 0 0) := by
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0
    (ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊) (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  apply integrable_finsetSum
  intro I hI
  convert (preTransparency := .instances) fourier_phase_integrable g
    (Real.log c+Real.log ((I.absNorm:ℝ)/D))
    ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
      logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
  funext v
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem polynomial_clipped_fourier (χ : Character) (inv : Bool)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D : ℝ) (hc : 0<c) (hD : 0<D)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y)) :
    polynomial χ inv (clippedTest W c θ) D 0 0=
      ∫v:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        polynomial χ inv (childLogTest Wref (θ+v)) D 0 0 := by
  let S:=ConcretePrimeRowBridge.idealsUpTo ⌈D*b⌉₊
  have hcover : ∀I : Ideal O,I≠0 → clippedTest W c θ ((I.absNorm:ℝ)/D)≠0 → I∈S := by
    intro I hI hi
    have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))) hD
    apply finite_source_cover Wref D b hD hWref I hI
    intro hz
    have he:=hagree _ hIp
    rw [hz,zero_mul] at he
    exact hi (by simp [clippedTest,childLogTest,←he])
  rw [polynomial_eq_finite χ inv (clippedTest W c θ) D 0 0 S hcover]
  simp_rw [polynomial_eq_finite χ inv (childLogTest Wref (θ+_)) D 0 0 S
    (child_cover Wref b D hD hWref _)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,Finset.mul_sum]
  have hint (I : Ideal O) : Integrable (fun v:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) v*
        ((D:ℂ)^(-(1/2:ℂ))*(coefficient χ inv I*childLogTest Wref (θ+v) ((I.absNorm:ℝ)/D)))) := by
    convert (preTransparency := .instances) fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log ((I.absNorm:ℝ)/D))
      ((D:ℂ)^(-(1/2:ℂ))*coefficient χ inv I*Wref ((I.absNorm:ℝ)/D)*
        logPhase θ (Real.log ((I.absNorm:ℝ)/D))) using 1
    funext v
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun I _=>hint I)]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hz : I=0
  · subst I
    simp only [coefficient_zero,zero_mul,mul_zero,integral_zero]
  have hIp : 0<(I.absNorm:ℝ)/D:=div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz))) hD
  rw [clipped_test_fourier W lo hi hlo hs hW Wref c θ _ hc hIp (hagree _ hIp),
    ←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  ring

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic InverseMoment InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeInverseAmplification

theorem polynomial_clipped_energy {ι : Type*} (rows : Finset ι)
    (χ : ι→Character) (inv : Bool) (A : ι→ℂ)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D E : ℝ) (J : ℕ) (hc : 0<c) (hD : 0<D) (hE : 0≤E)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y))
    (he : ∀s, (∑i∈rows,‖polynomial (χ i) inv (childLogTest Wref s) D 0 0*A i‖^2)
      ≤E*(1+‖s‖)^(2*J)) :
    (∑i∈rows,‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)≤
      E*(1+‖θ‖)^(2*J)*
        (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) v‖)^2 := by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let B:=density g (Real.log c)
  let φ : rows→ℝ→ℂ:=fun i v=>polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i
  have hint (i : rows) : Integrable (fun v:ℝ=>B v*φ i v) := by
    simpa only [B,φ,mul_assoc] using
      (polynomial_mode_integrable (χ i) inv g Wref b c θ D hD hWref).mul_const (A i)
  have hbound (v : ℝ) : (∑i:rows,‖φ i v‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖v‖)^J)^2 := by
    dsimp only [φ]
    rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i‖^2)]
    apply (he (θ+v)).trans
    have hh : 1+‖θ+v‖≤(1+‖θ‖)*(1+‖v‖) := by
      have hn:=norm_add_le θ v
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg v)]
    calc
      _≤E*((1+‖θ‖)*(1+‖v‖))^(2*J):=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden : Integrable (fun v:ℝ=>(1+‖v‖)^J*‖B v‖) := by
    simpa only [B,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy B φ
    (fun v:ℝ=>(1+‖v‖)^J) (by intro v;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq (i : rows) : (∫v:ℝ,B v*φ i v)=
      polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i := by
    rw [polynomial_clipped_fourier (χ i) inv W lo hi hlo hs hW Wref b c θ D hc hD hWref hagree,
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    dsimp [B,φ,g]
    ring
  simp_rw [heq] at hh
  rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)] at hh
  simpa only [B,density_norm,g] using hh

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory

namespace SevenEighths.DetectorDictionaryInverseMarkedUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseRawFourier InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeDetectorRawFiber

private theorem clipped_one_zero (W : ℝ→ℂ) : clippedTest W 1 0=W := by
  funext x
  simp [clippedTest,childLogTest,logPhase]

theorem moving_finite_energy (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type*}(rows : Finset ι)
      (χ : ι→Character)(A : ι→ℂ)(D E : ℝ),0<D→0≤E→
    (∀v : ℝ,(∑u∈rows,‖polynomial (χ u) true (childLogTest referenceWindow v) D 0 0*A u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀scaled reverse : Bool,∀n : ℕ,n≤2→∀U : ℝ,0<U→
    ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈rows,‖polynomial (χ u) true
      (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A u‖^2)
      ≤C*E*(1+‖t‖)^K := by
  obtain ⟨K,B,hB,hmass⟩:=familyDensity_moment J
  refine ⟨2*K,B^2,sq_pos_of_pos hB,?_⟩
  intro ι rows χ A D E hD hE href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  have hb:=polynomial_clipped_energy rows χ true A W (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t) (W.smooth ⊤)
    referenceWindow (13/4) 1 0 D E J (by norm_num) hD hE
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy) href
  rw [clipped_one_zero] at hb
  simp only [norm_zero,add_zero,one_pow,mul_one] at hb
  have hm:=hmass scaled reverse n hn U hU tstar r σ hσ t 1
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  apply hb.trans
  calc
    _≤E*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=>by positivity)) hm 2) hE
    _= _:=by rw [mul_pow,←pow_mul];ring_nf

theorem logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) :
    logTest W n=(HeckeDetectorRowwisePolynomial.logProfile^[n]) W := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [logTest,Function.iterate_succ_apply',←ih]

section Fiber
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_inverse_source
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (n : ℕ) (σ t : ℝ) :
    (inverseSourceSchwartz false false n U tstar F.r σ t : ℝ→ℂ)=
      twistProfile ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t := by
  funext x
  simpa only [Bool.false_eq_true,ite_false,HeckeDetectorCoefficientTransfer.orientedProfile,
    logTest_eq_iterate,Fiber.inverseProfile] using
    inverseSourceSchwartz_apply false false n U tstar F.r σ t x

theorem fiber_inverse_polynomial
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (selected : Finset Slot)
    (n : ℕ) (σ t : ℝ) (u : FreeRow) :
    polynomial (F.family u F.label) true
      (inverseSourceSchwartz false false n U tstar F.r σ t) (U^F.r) 0 0*
        F.physicalProduct selected u=
    polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u := by
  rw [fiber_inverse_source,polynomial_twistProfile]

end Fiber

theorem fiber_inverse_energy_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+‖t‖)^K := by
  obtain ⟨K,C,hC,hb⟩:=moving_finite_energy J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ t
  have hh:=hb F.rows (fun u=>F.family u F.label) (F.physicalProduct selected)
    (U^F.r) E (Real.rpow_pos_of_pos hU _) hE href false false n hn U hU tstar F.r σ hσ t
  simpa only [fiber_inverse_polynomial] using hh

theorem fiber_inverse_height_uniform_oai (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height→t∈Set.Icc (-height) height→
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+height)^K := by
  obtain ⟨K,C,hC,hb⟩:=fiber_inverse_energy_uniform J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ height t _ ht
  apply (hb F selected hU E hE href n hn σ hσ t).trans
  have hnorm : ‖t‖≤height := by simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  gcongr

end SevenEighths.DetectorDictionaryInverseMarkedUniform

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform_oai.{u_1, u_2} := @OAI.SevenEighths.DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform_oai.{u_1, u_2}
