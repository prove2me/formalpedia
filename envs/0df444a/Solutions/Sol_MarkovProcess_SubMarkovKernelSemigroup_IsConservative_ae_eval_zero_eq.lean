-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.ae_eval_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:19:43.933445+00:00
-- url     : https://prove2.me/submissions/fb2eebdc-87da-42c7-851f-85faec93495e

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative
end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
omit [LocallyCompactSpace alpha] in

theorem solution (hK : P.KolmogorovRegular hP) (x : alpha) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x), omega 0 = x := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  have hmap : (IsConservative.continuousProcess P hP x).map (fun omega ↦ omega 0) =
      Measure.dirac x := by
    rw [← Kernel.map_apply _ hmeas, IsConservative.continuousProcess_map_eval_zero P hP hK,
      Kernel.id_apply]
  rw [ae_iff]
  have hset : {omega : ContinuousPath alpha | ¬ omega 0 = x} =
      (fun omega : ContinuousPath alpha ↦ omega 0) ⁻¹' ({x}ᶜ : Set alpha) := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hset, ← Measure.map_apply hmeas (measurableSet_singleton x).compl, hmap,
    Measure.dirac_apply' _ (measurableSet_singleton x).compl,
    Set.indicator_of_notMem (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
      not_true_eq_false, not_false_eq_true])]
