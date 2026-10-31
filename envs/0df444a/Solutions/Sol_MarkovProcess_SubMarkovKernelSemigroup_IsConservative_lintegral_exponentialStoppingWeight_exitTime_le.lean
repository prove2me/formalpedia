-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.lintegral_exponentialStoppingWeight_exitTime_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:53:06.98031+00:00
-- url     : https://prove2.me/submissions/aa8935e4-1bed-4b66-8a4f-d1eb7a02cbe4

import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitTimeExponentialMoment_0f3c9ff2
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_measure_lt_exitTime_nsmul_le

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A positive exponential moment for the exit time

A uniform bound on the survival probability at one horizon `t0` propagates to the multiples of
that horizon by the Chapman--Kolmogorov law for the killed kernels: if the process started
anywhere survives the horizon `t0` inside the open set `U` with probability at most `q`, then it
survives `k` horizons with probability at most `q ^ k`
(`IsConservative.measure_lt_exitTime_nsmul_le`).  Summing the resulting geometric layers bounds a
*positive* exponential moment of the exit time
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le`), for every rate `lam` with
`q * exp (lam * t0) < 1`.

The positive exponential weight is `ContinuousPath.exponentialStoppingWeight`, which takes the
value `⊤` where the time is infinite.  That branch is forced: reading the extended time through
`ENNReal.toReal` would return `1` at `⊤` and silently discard the paths that never leave `U`.  A
finite integral of the weight therefore certifies almost-sure finiteness
(`ContinuousPath.ae_lt_top_of_lintegral_exponentialStoppingWeight_ne_top`), which the survival
bound supplies on its own
(`IsConservative.ae_exitTime_lt_top_of_measure_lt_exitTime_le`).

Two consequences are recorded.  An expected-exit-time bound `E_y τ_U ≤ M` valid from every
starting point supplies the survival hypothesis at the horizon `t0 = K M` with `q = K⁻¹` by
Markov's inequality, for every multiplier `K > 1`
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul`; the
multiplier `K = 2` is
`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le`), and a large
multiplier normalizes the moment to `2` at a rate that is still positive
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le`).  The
elementary pointwise bound `t ^ p ≤ (p / (lam * e)) ^ p * exp (lam * t)` converts an
exponential moment into every polynomial moment
(`IsConservative.lintegral_exitTime_pow_le`).

Every statement is an inequality of `ℝ≥0∞`-valued integrals; no integrability side condition and
no real-valued restatement appears.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]













end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



/-- The pointwise geometric layering behind the exponential moment: the exponential weight of an
extended time is dominated by one initial layer plus the layers indexed by the multiples of the
horizon which the time exceeds. -/
private theorem exponentialWeight_le_add_tsum (lam : ℝ) (hlam : 0 ≤ lam) (t0 : NNReal)
    (tau : ℝ≥0∞) :
    (if tau = ⊤ then ⊤ else ENNReal.ofReal (Real.exp (lam * tau.toReal))) ≤
      ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) +
        ∑' k : ℕ, ({u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator
          (fun _ ↦ ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) ^ (k + 2)) tau) := by
  classical
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) with ha
  have ha1 : 1 ≤ a := by
    rw [ha, ENNReal.one_le_ofReal]
    exact Real.one_le_exp (mul_nonneg hlam t0.coe_nonneg)
  have hpow : ∀ m : ℕ, ENNReal.ofReal (Real.exp (lam * ((m • t0 : NNReal) : ℝ))) = a ^ m := by
    intro m
    rw [ha, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    push_cast [nsmul_eq_mul]
    ring
  by_cases hall : ∀ m : ℕ, ((m • t0 : NNReal) : ℝ≥0∞) < tau
  · have hterm : ∀ k : ℕ, (1 : ℝ≥0∞) ≤
        {u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator (fun _ ↦ a ^ (k + 2)) tau := by
      intro k
      have hmem : tau ∈ {u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u} := hall (k + 1)
      rw [Set.indicator_of_mem hmem]
      exact one_le_pow₀ ha1
    have htop : (∑' k : ℕ, ({u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator
        (fun _ ↦ a ^ (k + 2)) tau)) = ⊤ := by
      refine top_unique ?_
      calc
        (⊤ : ℝ≥0∞) = ∑' _k : ℕ, (1 : ℝ≥0∞) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
        _ ≤ _ := ENNReal.tsum_le_tsum hterm
    rw [htop, add_top]
    exact le_top
  · push Not at hall
    obtain ⟨m0, hm0⟩ := hall
    have hex : ∃ m : ℕ, tau ≤ ((m • t0 : NNReal) : ℝ≥0∞) := ⟨m0, hm0⟩
    set m := Nat.find hex with hm
    have hmspec : tau ≤ ((m • t0 : NNReal) : ℝ≥0∞) := Nat.find_spec hex
    have hne : tau ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hmspec
    rw [if_neg hne]
    have hle : ENNReal.ofReal (Real.exp (lam * tau.toReal)) ≤ a ^ m := by
      rw [← hpow m]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      refine mul_le_mul_of_nonneg_left ?_ hlam
      exact (ENNReal.toReal_le_coe_of_le_coe hmspec)
    refine hle.trans ?_
    match hmatch : m with
    | 0 => simpa only [pow_zero] using le_add_right ha1
    | 1 => simpa only [pow_one] using le_add_right le_rfl
    | (j + 2) =>
        have hlt : ((((j + 1) : ℕ) • t0 : NNReal) : ℝ≥0∞) < tau := by
          have := Nat.find_min hex (m := j + 1) (by omega)
          exact not_le.mp this
        refine le_add_left ?_
        refine le_trans (le_of_eq ?_)
          (ENNReal.le_tsum (f := fun k : ℕ ↦
            {u : ℝ≥0∞ | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < u}.indicator
              (fun _ ↦ a ^ (k + 2)) tau) j)
        have hmem : tau ∈ {u : ℝ≥0∞ | (((j + 1) • t0 : NNReal) : ℝ≥0∞) < u} := hlt
        rw [Set.indicator_of_mem hmem]















end

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A positive exponential moment for the exit time

A uniform bound on the survival probability at one horizon `t0` propagates to the multiples of
that horizon by the Chapman--Kolmogorov law for the killed kernels: if the process started
anywhere survives the horizon `t0` inside the open set `U` with probability at most `q`, then it
survives `k` horizons with probability at most `q ^ k`
(`IsConservative.measure_lt_exitTime_nsmul_le`).  Summing the resulting geometric layers bounds a
*positive* exponential moment of the exit time
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le`), for every rate `lam` with
`q * exp (lam * t0) < 1`.

The positive exponential weight is `ContinuousPath.exponentialStoppingWeight`, which takes the
value `⊤` where the time is infinite.  That branch is forced: reading the extended time through
`ENNReal.toReal` would return `1` at `⊤` and silently discard the paths that never leave `U`.  A
finite integral of the weight therefore certifies almost-sure finiteness
(`ContinuousPath.ae_lt_top_of_lintegral_exponentialStoppingWeight_ne_top`), which the survival
bound supplies on its own
(`IsConservative.ae_exitTime_lt_top_of_measure_lt_exitTime_le`).

Two consequences are recorded.  An expected-exit-time bound `E_y τ_U ≤ M` valid from every
starting point supplies the survival hypothesis at the horizon `t0 = K M` with `q = K⁻¹` by
Markov's inequality, for every multiplier `K > 1`
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le_mul`; the
multiplier `K = 2` is
`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le`), and a large
multiplier normalizes the moment to `2` at a rate that is still positive
(`IsConservative.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le`).  The
elementary pointwise bound `t ^ p ≤ (p / (lam * e)) ^ p * exp (lam * t)` converts an
exponential moment into every polynomial moment
(`IsConservative.lintegral_exitTime_pow_le`).

Every statement is an inequality of `ℝ≥0∞`-valued integrals; no integrability side condition and
no real-valued restatement appears.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (q : ℝ≥0∞) (t0 : NNReal) (lam : ℝ) (hlam : 0 ≤ lam)
    (hcontr : q * ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) < 1)
    (hq : ∀ y, IsConservative.continuousProcess P hP y
      {omega | (t0 : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ q)
    (x : alpha) :
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
        ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) *
        (1 - q * ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))))⁻¹ := by
  classical
  set Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x with hQ
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * (t0 : ℝ))) with ha
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  set B : ℕ → Set (ContinuousPath alpha) := fun k ↦
    {omega | (((k + 1) • t0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} with hB
  have hBmeas : ∀ k, MeasurableSet (B k) := fun k ↦ measurableSet_lt measurable_const hExit
  have hpoint : ∀ omega : ContinuousPath alpha,
      ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega ≤
        a + ∑' k : ℕ, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega := by
    intro omega
    have h := exponentialWeight_le_add_tsum lam hlam t0 (ContinuousPath.exitTime U omega)
    refine h.trans (le_of_eq ?_)
    congr 1
  have hlayer : ∀ k : ℕ, ∫⁻ omega, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega ∂Q ≤
      a ^ (k + 2) * q ^ (k + 1) := by
    intro k
    rw [lintegral_indicator_const (hBmeas k)]
    exact mul_le_mul_right (hP.measure_lt_exitTime_nsmul_le P hFeller hK U hU q t0 hq (k + 1) x)
      (a ^ (k + 2))
  have hsum : (∑' k : ℕ, a ^ (k + 2) * q ^ (k + 1)) = a * ((a * q) * (1 - a * q)⁻¹) := by
    rw [← ENNReal.tsum_geometric_add_one (a * q), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun k ↦ ?_
    rw [mul_pow, ← mul_assoc, ← pow_succ']
  have hcontr' : a * q < 1 := by rwa [mul_comm]
  have hfinal : a + a * ((a * q) * (1 - a * q)⁻¹) = a * (1 - q * a)⁻¹ := by
    have hne : (1 : ℝ≥0∞) - a * q ≠ 0 := by
      simp only [ne_eq, tsub_eq_zero_iff_le, not_le]
      exact hcontr'
    have htop : (1 : ℝ≥0∞) - a * q ≠ ⊤ := by
      exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hid : (1 : ℝ≥0∞) - a * q + a * q = 1 := tsub_add_cancel_of_le hcontr'.le
    have hgeom : (1 : ℝ≥0∞) + (a * q) * (1 - a * q)⁻¹ = (1 - a * q)⁻¹ := by
      calc
        (1 : ℝ≥0∞) + (a * q) * (1 - a * q)⁻¹
            = (1 - a * q) * (1 - a * q)⁻¹ + (a * q) * (1 - a * q)⁻¹ := by
          rw [ENNReal.mul_inv_cancel hne htop]
        _ = ((1 - a * q) + a * q) * (1 - a * q)⁻¹ := (add_mul _ _ _).symm
        _ = (1 - a * q)⁻¹ := by rw [hid, one_mul]
    calc
      a + a * ((a * q) * (1 - a * q)⁻¹) = a * (1 + (a * q) * (1 - a * q)⁻¹) := by ring
      _ = a * (1 - a * q)⁻¹ := by rw [hgeom]
      _ = a * (1 - q * a)⁻¹ := by rw [mul_comm a q]
  calc
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega ∂Q
        ≤ ∫⁻ omega, (a + ∑' k : ℕ, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega) ∂Q :=
      lintegral_mono hpoint
    _ = a + ∫⁻ omega, ∑' k : ℕ, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega ∂Q := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ = a + ∑' k : ℕ, ∫⁻ omega, (B k).indicator (fun _ ↦ a ^ (k + 2)) omega ∂Q := by
      rw [lintegral_tsum fun k ↦ (measurable_const.indicator (hBmeas k)).aemeasurable]
    _ ≤ a + ∑' k : ℕ, a ^ (k + 2) * q ^ (k + 1) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum hlayer)
    _ = a + a * ((a * q) * (1 - a * q)⁻¹) := by rw [hsum]
    _ = a * (1 - q * a)⁻¹ := hfinal
