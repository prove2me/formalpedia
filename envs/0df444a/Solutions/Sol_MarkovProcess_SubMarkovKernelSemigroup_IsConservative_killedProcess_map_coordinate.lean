-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:51:51.254775+00:00
-- url     : https://prove2.me/submissions/1f4fdd3c-860c-40c5-93f9-bc748a4da84a

import Definitions.Def_MarkovProcess_V3H_Killed_KillAtExit_9c0394fb
import Definitions.Def_MarkovProcess_V3H_Killed_Process_a15f3c27
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
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
import Theorems.Thm_MarkovProcess_ContinuousPath_measurable_coordinate_killAtExit
import Theorems.Thm_MarkovProcess_ContinuousPath_preimage_coordinate_killAtExit_of_mem

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The process killed at the exit of an open set, as a law on lifetime paths

For the continuous-path process `Q = continuousProcess P hP` of a conservative semigroup and an
open set `U`, killing each path at its exit time from `U` produces a Markov kernel

  `killedProcess P hP U hU : Kernel U (LifetimePath U)`,

the law of the process started inside `U` and sent to the cemetery when it leaves `U`.  It is the
image of `Q` under `ContinuousPath.killAtExit U`, pulled back to the carrier `U`.

Two marginals are identified here.  The lifetime of the killed process is the exit time
(`killedProcess_map_lifetime`), and its coordinate at a fixed time is the cemetery extension of
the killed transition kernel on `U` (`killedProcess_map_coordinate`): the live part is
`killedKernelOn P hP U hU t x` and the cemetery carries exactly the mass lost by time `t`.

No finite-dimensional distribution of the killed process is identified here, and no Feller or
regularity property of the killed family is claimed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath



end LifetimePath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)







/-- The killed process started at `x ∈ U` is the law of the process started at `x`, pushed forward
by killing at the exit time of `U`. -/
theorem IsConservative.killedProcess_apply (x : U) :
    IsConservative.killedProcess P hP U hU x =
      (IsConservative.continuousProcess P hP (x : alpha)).map (ContinuousPath.killAtExit U) := by
  rw [IsConservative.killedProcess_eq_map,
    Kernel.map_apply _ (ContinuousPath.measurable_killAtExit U hU), Kernel.comap_apply]



/-- The law of the killed process, read through the coordinate at a fixed time. -/
theorem IsConservative.killedProcess_map_coordinate_eq (t : NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map (LifetimePath.coordinate t) =
      (IsConservative.continuousProcess P hP (x : alpha)).map
        (fun omega ↦ LifetimePath.coordinate t (ContinuousPath.killAtExit U omega)) := by
  rw [IsConservative.killedProcess_apply P hP U hU x,
    Measure.map_map (LifetimePath.measurable_coordinate t)
      (ContinuousPath.measurable_killAtExit U hU)]
  rfl

/-- The total mass of the killed transition kernel on `U` is the survival probability. -/
theorem IsConservative.killedKernelOn_univ_eq_continuousProcess (t : NNReal) (x : U) :
    IsConservative.killedKernelOn P hP U hU t x Set.univ =
      IsConservative.continuousProcess P hP (x : alpha)
        {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} := by
  have hsum : IsConservative.killedKernel P hP U hU t (x : alpha) U +
      IsConservative.killedKernel P hP U hU t (x : alpha) Uᶜ =
        IsConservative.killedKernel P hP U hU t (x : alpha) Set.univ :=
    measure_add_measure_compl hU.measurableSet
  rw [IsConservative.killedKernel_apply_compl P hP U hU t (x : alpha), add_zero,
    IsConservative.killedKernel_apply_univ P hP U hU t (x : alpha)] at hsum
  rw [IsConservative.killedKernelOn_apply_univ P hP U hU t x, hsum]



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
# The process killed at the exit of an open set, as a law on lifetime paths

For the continuous-path process `Q = continuousProcess P hP` of a conservative semigroup and an
open set `U`, killing each path at its exit time from `U` produces a Markov kernel

  `killedProcess P hP U hU : Kernel U (LifetimePath U)`,

the law of the process started inside `U` and sent to the cemetery when it leaves `U`.  It is the
image of `Q` under `ContinuousPath.killAtExit U`, pulled back to the carrier `U`.

Two marginals are identified here.  The lifetime of the killed process is the exit time
(`killedProcess_map_lifetime`), and its coordinate at a fixed time is the cemetery extension of
the killed transition kernel on `U` (`killedProcess_map_coordinate`): the live part is
`killedKernelOn P hP U hU t x` and the cemetery carries exactly the mass lost by time `t`.

No finite-dimensional distribution of the killed process is identified here, and no Feller or
regularity property of the killed family is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)















namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (t : NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map (LifetimePath.coordinate t) =
      Kernel.cemeteryExtension (IsConservative.killedKernelOn P hP U hU t)
        (Cemetery.alive x) := by
  rw [IsConservative.killedProcess_map_coordinate_eq P hP U hU t x]
  refine Measure.ext fun S hS ↦ ?_
  have hC : MeasurableSet (Cemetery.alive ⁻¹' S : Set U) := measurable_inl hS
  have hlive : IsConservative.continuousProcess P hP (x : alpha) {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧
      omega t ∈ Subtype.val '' (Cemetery.alive ⁻¹' S)} =
      IsConservative.killedKernelOn P hP U hU t x (Cemetery.alive ⁻¹' S) :=
    (IsConservative.killedKernelOn_apply_eq_continuousProcess P hP U hU t x hC).symm
  have hdead : IsConservative.continuousProcess P hP (x : alpha) {omega : ContinuousPath alpha |
      ¬ (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} =
      1 - IsConservative.killedKernelOn P hP U hU t x Set.univ := by
    rw [IsConservative.killedKernelOn_univ_eq_continuousProcess P hP U hU t x]
    exact prob_compl_eq_one_sub (ContinuousPath.measurableSet_lt_exitTime U hU t)
  rw [Measure.map_apply (ContinuousPath.measurable_coordinate_killAtExit U hU t) hS,
    Kernel.cemeteryExtension_alive_apply' _ x hS]
  by_cases hdelta : (Cemetery.delta : Cemetery U) ∈ S
  · rw [ContinuousPath.preimage_coordinate_killAtExit_of_mem U t hdelta,
      Set.indicator_of_mem hdelta, Pi.one_apply, mul_one]
    have hdisj : Disjoint
        {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega ∧
          omega t ∈ Subtype.val '' (Cemetery.alive ⁻¹' S)}
        {omega : ContinuousPath alpha | ¬ (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} :=
      Set.disjoint_left.mpr fun omega homega hbad ↦ hbad homega.1
    rw [measure_union hdisj
      ((ContinuousPath.measurableSet_lt_exitTime U hU t).compl), hlive, hdead]
  · rw [ContinuousPath.preimage_coordinate_killAtExit_of_notMem U t hdelta,
      Set.indicator_of_notMem hdelta, mul_zero, add_zero, hlive]
