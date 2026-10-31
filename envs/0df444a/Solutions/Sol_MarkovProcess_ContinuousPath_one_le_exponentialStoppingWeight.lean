-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.one_le_exponentialStoppingWeight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:36:05.379911+00:00
-- url     : https://prove2.me/submissions/5aa00772-54f8-4929-b14a-3af66d4e253f

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



/-- On the finite branch the exponential weight is the ordinary exponential. -/
theorem exponentialStoppingWeight_of_ne_top (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    {omega : ContinuousPath alpha} (h : sigma omega ≠ ⊤) :
    exponentialStoppingWeight lam sigma omega =
      ENNReal.ofReal (Real.exp (lam * (sigma omega).toReal)) :=
  if_neg h

/-- On the infinite branch the exponential weight is `⊤`. -/
theorem exponentialStoppingWeight_of_eq_top (lam : ℝ) (sigma : ContinuousPath alpha → ℝ≥0∞)
    {omega : ContinuousPath alpha} (h : sigma omega = ⊤) :
    exponentialStoppingWeight lam sigma omega = ⊤ :=
  if_pos h







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
open MarkovProcess.ContinuousPath
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



variable {alpha : Type*} [TopologicalSpace alpha]







namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution (lam : ℝ) (hlam : 0 ≤ lam)
    (sigma : ContinuousPath alpha → ℝ≥0∞) (omega : ContinuousPath alpha) :
    1 ≤ exponentialStoppingWeight lam sigma omega := by
  by_cases h : sigma omega = ⊤
  · rw [exponentialStoppingWeight_of_eq_top lam sigma h]
    exact le_top
  · rw [exponentialStoppingWeight_of_ne_top lam sigma h, ENNReal.one_le_ofReal]
    exact Real.one_le_exp (mul_nonneg hlam ENNReal.toReal_nonneg)
