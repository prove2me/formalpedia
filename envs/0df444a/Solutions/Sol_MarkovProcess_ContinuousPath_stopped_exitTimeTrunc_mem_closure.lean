-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.stopped_exitTimeTrunc_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:49:48.467173+00:00
-- url     : https://prove2.me/submissions/a29a6fa0-7fe2-4220-87a6-832938df3ee6

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
import Theorems.Thm_MarkovProcess_ContinuousPath_coordinate_exitTime_mem_frontier

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



/-- The `WithTop`-valued exit time is the exit time. -/
theorem exitTimeTop_apply (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTimeTop U omega = exitTime U omega := rfl







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







end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)









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



variable {alpha : Type*} [PseudoMetricSpace alpha]



namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution (U : Set alpha) (hU : IsOpen U) (K : NNReal)
    (omega : ContinuousPath alpha) (h0 : omega 0 ∈ U) :
    omega (exitTimeTrunc U K omega) ∈ closure U := by
  rcases lt_or_ge (K : ℝ≥0∞) (exitTime U omega) with hK | hexit
  · have hT : exitTimeTrunc U K omega = K := by
      apply WithTop.coe_injective
      rw [coe_exitTimeTrunc, exitTimeTop_apply]
      exact min_eq_right hK.le
    rw [hT]
    exact subset_closure (mem_of_lt_exitTime U omega K hK)
  · have hfin : exitTime U omega ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hexit
    have hT : exitTimeTrunc U K omega = (exitTime U omega).toNNReal := by
      apply ENNReal.coe_injective
      rw [coe_exitTimeTrunc_ennreal, min_eq_left hexit, ENNReal.coe_toNNReal hfin]
    rw [hT]
    exact (hU.frontier_eq ▸ coordinate_exitTime_mem_frontier U hU omega h0 hfin).1
