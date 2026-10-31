-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.measure_lt_exitTime_nsmul_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:38:14.919017+00:00
-- url     : https://prove2.me/submissions/5c7e8d2a-4bda-42e8-9f52-9c3e00f29c11

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedKernel_add

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
    (U : Set alpha) (hU : IsOpen U) (q : ℝ≥0∞) (t0 : NNReal)
    (hq : ∀ y, IsConservative.continuousProcess P hP y
      {omega | (t0 : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ q)
    (k : ℕ) (x : alpha) :
    IsConservative.continuousProcess P hP x
        {omega | ((k • t0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} ≤ q ^ k := by
  have hstep : ∀ y, IsConservative.killedKernel P hP U hU t0 y Set.univ ≤ q := by
    intro y
    rw [IsConservative.killedKernel_apply_univ]
    exact hq y
  have hkey : ∀ (n : ℕ) (y : alpha),
      IsConservative.killedKernel P hP U hU (n • t0) y Set.univ ≤ q ^ n := by
    intro n
    induction n with
    | zero =>
        intro y
        rw [pow_zero, zero_nsmul, IsConservative.killedKernel_apply_univ]
        exact prob_le_one
    | succ n ih =>
        intro y
        rw [succ_nsmul, IsConservative.killedKernel_add P hP U hU hFeller hK (n • t0) t0,
          Kernel.comp_apply' _ _ _ MeasurableSet.univ]
        calc
          ∫⁻ z, IsConservative.killedKernel P hP U hU t0 z Set.univ
              ∂(IsConservative.killedKernel P hP U hU (n • t0) y)
              ≤ ∫⁻ _z, q ∂(IsConservative.killedKernel P hP U hU (n • t0) y) :=
            lintegral_mono hstep
          _ = q * IsConservative.killedKernel P hP U hU (n • t0) y Set.univ := by
            rw [lintegral_const]
          _ ≤ q * q ^ n := mul_le_mul_right (ih y) q
          _ = q ^ (n + 1) := by rw [pow_succ, mul_comm]
  have hx := hkey k x
  rwa [IsConservative.killedKernel_apply_univ] at hx
