-- Prove2me | solution 1 for MarkovProcess.tendsto_integral_continuousPath_finiteEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:07:30.941446+00:00
-- url     : https://prove2.me/submissions/57df9b4d-addd-41e6-b831-0cc88860f24c

import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_DenseTime_Trajectory
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_PositiveC0OperatorMeasure
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_Polish_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Definitions.Def_MarkovProcess_Trajectory_AllTimeFiniteMarginals
import Definitions.Def_MarkovProcess_Trajectory_Basic
import Definitions.Def_MarkovProcess_Trajectory_FiniteMarginals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess

variable {α : Type*} [TopologicalSpace α]





namespace PositiveC0OperatorMeasure







@[simp]
theorem compactlySupportedToC0LinearMap_apply (f : C_c(α, ℝ)) (x : α) :
    compactlySupportedToC0LinearMap f x = f x :=
  rfl
end PositiveC0OperatorMeasure
end MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Arbitrary-time finite marginals of continuous-path trajectories

This file develops the simultaneous rational approximation needed to pass from the already
identified rational finite-dimensional distributions to finite families of arbitrary
nonnegative real times.  It proves the path-side dominated-convergence argument, identifies every
rational approximating law with the existing finite-set kernel, and reduces the desired equality
to compactly-supported-test convergence of those finite-set kernels.

The remaining Feller analytic statement is not claimed here: one must still prove that the
recursively composed finite-time kernels have that convergence under simultaneous convergence of
their strictly ordered time coordinates.  No continuous-time Markov or Hunt property is assumed
or asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal


noncomputable section










/-- Simultaneous evaluation at finitely many fixed times is continuous in the path. -/
theorem MarkovProcess.ContinuousPath.continuous_finiteEvaluation {ι α : Type*} [Finite ι]
    [TopologicalSpace α] (τ : ι → NNReal) :
    Continuous (finiteEvaluation (α := α) τ) := by
  apply continuous_pi
  intro i
  exact continuous_eval (alpha := α) (τ i)

/-- If each time in a finite family converges, then simultaneous evaluation along any
continuous path converges in the finite product topology. -/
theorem MarkovProcess.ContinuousPath.tendsto_finiteEvaluation {ι α : Type*} [Finite ι]
    [TopologicalSpace α] (τ : ι → NNReal) (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i)))
    (path : ContinuousPath α) :
    Tendsto (fun k ↦ finiteEvaluation (α := α) (q k) path) atTop
      (nhds (finiteEvaluation (α := α) τ path)) := by
  apply tendsto_pi_nhds.2
  intro i
  exact Filter.Tendsto.comp path.continuous.continuousAt (hq i)



variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]



omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
  [LocallyCompactSpace α] in

theorem solution
    {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (K : Kernel β (ContinuousPath α)) (hK : IsMarkovKernel K)
    (x : β) (f : CompactlySupportedContinuousMap (ι → α) ℝ)
    (τ : ι → NNReal)
    (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i))) :
    Tendsto
      (fun k ↦ ∫ path, f (ContinuousPath.finiteEvaluation (α := α) (q k) path) ∂K x)
      atTop
      (nhds (∫ path, f (ContinuousPath.finiteEvaluation (α := α) τ path) ∂K x)) := by
  let : IsMarkovKernel K := hK
  let f0 : ZeroAtInftyContinuousMap (ι → α) ℝ :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [] with k
    exact (f.continuous.comp
      (ContinuousPath.continuous_finiteEvaluation (q k))).aestronglyMeasurable
  · refine ⟨‖f0‖, Filter.Eventually.of_forall fun k ↦ ?_⟩
    filter_upwards [] with path
    simpa only [f0, PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply,
      Real.norm_eq_abs] using! f0.toBCF.norm_coe_le_norm
      (ContinuousPath.finiteEvaluation (α := α) (q k) path)
  · filter_upwards [] with path
    exact Filter.Tendsto.comp f.continuous.continuousAt
      (ContinuousPath.tendsto_finiteEvaluation τ q hq path)
