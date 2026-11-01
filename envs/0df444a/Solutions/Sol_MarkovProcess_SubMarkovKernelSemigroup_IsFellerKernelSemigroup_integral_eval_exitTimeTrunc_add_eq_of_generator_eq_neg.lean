-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_eval_exitTimeTrunc_add_eq_of_generator_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:33:17.928553+00:00
-- url     : https://prove2.me/submissions/e4f7d975-571b-488e-a703-62fa113aee96

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integral_eval_stoppingTime_sub_eq_integral_integral_generator

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times of open sets on continuous-path space

For an open set `U` this file studies `ContinuousPath.exitTime U`, the first time a continuous
path leaves `U`, in the `WithTop`-valued form `ContinuousPath.exitTimeTop U` demanded by
Mathlib's stopping-time convention.  The main consumer facts are: the exit time is a stopping
time for the canonical filtration; it is finite exactly when the path leaves `U` at some time;
at a finite exit time the path sits on the frontier of `U` when it started inside; and its
truncation `exitTimeTrunc U K` at a deterministic horizon is an `NNReal`-valued stopping time,
which is the form the finite-stopping-time API of this library consumes.  The generic time-set
identities `survivalSet_top`, `survivalSet_ne_top`, and `survivalSet` identify the positive real
times below an extended nonnegative horizon.

The route is the closed-set detection of `Path/ClosedSetDetection.lean`: the event
`{exitTime ≤ t}` is the event of hitting the closed set `Uᶜ` by time `t`, because a path that
stays in the open set `U` throughout `[0, t]` stays in it slightly beyond `t`.

This file constructs no probability law and proves no probabilistic statement; in particular it
does not claim that the exit time is almost surely finite for any process.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MarkovProcess

namespace ContinuousPath

noncomputable section

section SurvivalSets







end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order











end Order

section WithTopValue









/-- The truncated exit time never exceeds its horizon. -/
theorem exitTimeTrunc_le (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    exitTimeTrunc U K omega ≤ K := by
  rw [← WithTop.coe_le_coe, coe_exitTimeTrunc]
  exact min_le_right _ _

end WithTopValue

section Frontier





end Frontier

section Stopping

variable [MeasurableSpace alpha] [BorelSpace alpha]





end Stopping

end

end ContinuousPath

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The expected exit time, untruncated

The expected exit time bound of `Trajectory/DynkinStopping.lean` is stated for the exit time
truncated at a deterministic horizon `K`, uniformly in `K`.  This file removes the truncation by
monotone convergence: under the same hypotheses (`L f ≤ -1` on the open set `U`, `f ≥ m`),

  `E_x τ_U ≤ f x - m`  (`IsFellerKernelSemigroup.lintegral_exitTime_le`),

as an `ℝ≥0∞`-valued integral of the `ℝ≥0∞`-valued exit time, so in particular the exit time from
`U` is almost surely finite from every starting point (`ae_exitTime_lt_top`).

It also records that the truncated exit time of `Path/ExitTime.lean` is the generic truncation
`StoppingTime.truncTime` of `Trajectory/StoppingLtTop.lean` applied to `exitTimeTop`
(`ContinuousPath.exitTimeTrunc_eq_truncTime`), and the monotone limit
`ContinuousPath.iSup_exitTimeTrunc : ⨆ n, exitTimeTrunc U n ω = exitTime U ω`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



/-- The truncated exit time, read in `ℝ≥0∞`, is the minimum of the exit time and the horizon. -/
theorem coe_exitTimeTrunc_ennreal (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha) :
    ((exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) = min (exitTime U omega) (K : ℝ≥0∞) :=
  coe_exitTimeTrunc U K omega





end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}









end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Harmonic and Poisson representations, and the localized Dynkin formula

Consequences of Dynkin's formula at the exit time of an open set `U` truncated at a horizon `K`
(`Trajectory/DynkinStopping.lean`), for the continuous-path process `Q` of a conservative Feller
semigroup and `f` in the generator domain of its `C₀` semigroup, with generator `L f`:

* `integral_eval_exitTimeTrunc_eq_of_generator_eq_zero` (**harmonic representation**): if
  `L f = 0` on `U`, then `E_x f(ω_{τ ∧ K}) = f x`;
* `integral_eval_exitTimeTrunc_add_eq_of_generator_eq_neg` (**Poisson representation**): if
  `L f = -g` on `U`, then `E_x f(ω_{τ ∧ K}) + E_x ∫_0^{τ ∧ K} g(ω_s) ds = f x`;
* `stopped_exitTimeTrunc_mem_closure`: from a starting point in `U`, the position at `τ ∧ K` lies
  in the closure of `U`, so a continuous function that agrees with `f` on the closure of `U`
  has the same stopped expectation; this gives the **localized Dynkin formula**
  `integral_eval_exitTimeTrunc_sub_eq_of_eqOn_closure`, which is how test functions outside `C₀`
  (agreeing with a domain element near the closure of a bounded set) enter moment identities.

The integrand of Dynkin's formula is only ever evaluated strictly before the exit time, where the
path is inside `U`; this is the observation behind all three statements.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Strictly before the truncated exit time the path is inside `U`. -/
theorem mem_of_lt_exitTimeTrunc (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha)
    {s : NNReal} (hs : s < exitTimeTrunc U K omega) : omega s ∈ U := by
  apply mem_of_lt_exitTime U omega s
  have h : ((s : NNReal) : ℝ≥0∞) < ((exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr hs
  rw [coe_exitTimeTrunc_ennreal] at h
  exact lt_of_lt_of_le h (min_le_left _ _)



/-- The time integral of a function of the path up to the truncated exit time only sees the values
of the function on `U`: two functions agreeing on `U` give the same integral. -/
theorem integral_exitTimeTrunc_congr (U : Set alpha) (K : NNReal)
    {g₁ g₂ : alpha → ℝ} (hg : Set.EqOn g₁ g₂ U) (omega : ContinuousPath alpha) :
    ∫ s in (0 : ℝ)..(exitTimeTrunc U K omega : ℝ), g₁ (omega (Real.toNNReal s)) =
      ∫ s in (0 : ℝ)..(exitTimeTrunc U K omega : ℝ),
        g₂ (omega (Real.toNNReal s)) := by
  rw [intervalIntegral.integral_of_le NNReal.zero_le_coe,
    intervalIntegral.integral_of_le NNReal.zero_le_coe,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
  refine hg (mem_of_lt_exitTimeTrunc U K omega ?_)
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal s hs.1.le]
  exact hs.2

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)









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
# Harmonic and Poisson representations, and the localized Dynkin formula

Consequences of Dynkin's formula at the exit time of an open set `U` truncated at a horizon `K`
(`Trajectory/DynkinStopping.lean`), for the continuous-path process `Q` of a conservative Feller
semigroup and `f` in the generator domain of its `C₀` semigroup, with generator `L f`:

* `integral_eval_exitTimeTrunc_eq_of_generator_eq_zero` (**harmonic representation**): if
  `L f = 0` on `U`, then `E_x f(ω_{τ ∧ K}) = f x`;
* `integral_eval_exitTimeTrunc_add_eq_of_generator_eq_neg` (**Poisson representation**): if
  `L f = -g` on `U`, then `E_x f(ω_{τ ∧ K}) + E_x ∫_0^{τ ∧ K} g(ω_s) ds = f x`;
* `stopped_exitTimeTrunc_mem_closure`: from a starting point in `U`, the position at `τ ∧ K` lies
  in the closure of `U`, so a continuous function that agrees with `f` on the closure of `U`
  has the same stopped expectation; this gives the **localized Dynkin formula**
  `integral_eval_exitTimeTrunc_sub_eq_of_eqOn_closure`, which is how test functions outside `C₀`
  (agreeing with a domain element near the closure of a bounded set) enter moment identities.

The integrand of Dynkin's formula is only ever evaluated strictly before the exit time, where the
path is inside `U`; this is the observation behind all three statements.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)





namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    {g : alpha → ℝ} (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y = -g y) (K : NNReal)
    (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) +
      ∫ omega, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
          g (omega (Real.toNNReal s))) ∂(IsConservative.continuousProcess P hP x) =
      (f : C₀(alpha, ℝ)) x := by
  have hdynkin := hFeller.integral_eval_stoppingTime_sub_eq_integral_integral_generator hP hK f
    (ContinuousPath.exitTimeTrunc U K) (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)
    (ContinuousPath.exitTimeTrunc_le U K) x
  have hneg : ∀ omega : ContinuousPath alpha,
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) =
      -∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
        g (omega (Real.toNNReal s)) := by
    intro omega
    rw [ContinuousPath.integral_exitTimeTrunc_congr U K (g₂ := fun y ↦ -g y) (fun y hy ↦ hLf y hy) omega,
      intervalIntegral.integral_neg]
  simp only [hneg, integral_neg] at hdynkin
  linarith only [hdynkin]
