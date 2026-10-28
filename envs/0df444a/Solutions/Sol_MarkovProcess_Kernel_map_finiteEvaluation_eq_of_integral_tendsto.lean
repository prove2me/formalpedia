-- Prove2me | solution 1 for MarkovProcess.Kernel.map_finiteEvaluation_eq_of_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:09:33.072257+00:00
-- url     : https://prove2.me/submissions/c52d0351-5676-4df4-ba35-5433b61b03db

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
import Theorems.Thm_MarkovProcess_tendsto_integral_continuousPath_finiteEvaluation
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
















variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]

omit [SecondCountableTopology α] [LocallyCompactSpace α] in
/-- Simultaneous evaluation at finitely many fixed times is Borel measurable. -/
theorem MarkovProcess.ContinuousPath.measurable_finiteEvaluation {ι : Type*} [Finite ι]
    (τ : ι → NNReal) : Measurable (finiteEvaluation (α := α) τ) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_coordinateProcess (alpha := α) (τ i)




theorem solution
    {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    (K : Kernel β (ContinuousPath α)) (hK : IsMarkovKernel K)
    (Lseq : ℕ → Kernel β (ι → α)) (L : Kernel β (ι → α))
    (hL : IsMarkovKernel L) (τ : ι → NNReal) (q : ℕ → ι → NNReal)
    (hq : ∀ i, Tendsto (fun k ↦ q k i) atTop (nhds (τ i)))
    (hlaw : ∀ k, K.map (ContinuousPath.finiteEvaluation (q k)) = Lseq k)
    (hfinite : ∀ (x : β) (f : CompactlySupportedContinuousMap (ι → α) ℝ),
      Tendsto (fun k ↦ ∫ y, f y ∂Lseq k x) atTop (nhds (∫ y, f y ∂L x))) :
    K.map (ContinuousPath.finiteEvaluation τ) = L := by
  let : IsMarkovKernel K := hK
  let : IsMarkovKernel L := hL
  apply Kernel.ext
  intro x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hpath := tendsto_integral_continuousPath_finiteEvaluation
    K hK x f τ q hq
  have heq : ∀ k,
      (∫ path, f (ContinuousPath.finiteEvaluation (q k) path) ∂K x) =
        ∫ y, f y ∂Lseq k x := by
    intro k
    have hm := congrArg (fun κ : Kernel β (ι → α) ↦ κ x) (hlaw k)
    have hi := congrArg (fun μ : Measure (ι → α) ↦ ∫ y, f y ∂μ) hm
    change (∫ y, f y ∂(K.map (ContinuousPath.finiteEvaluation (q k))) x) =
      ∫ y, f y ∂Lseq k x at hi
    have heval : Measurable (ContinuousPath.finiteEvaluation (α := α) (q k)) :=
      ContinuousPath.measurable_finiteEvaluation (q k)
    have hmap :
        (K.map (ContinuousPath.finiteEvaluation (q k))) x =
          (K x).map (ContinuousPath.finiteEvaluation (q k)) :=
      Kernel.map_apply K heval x
    rw [hmap, integral_map] at hi
    · exact hi
    · exact heval.aemeasurable
    · exact f.continuous.aestronglyMeasurable
  have hsame :
      (fun k ↦ ∫ path, f (ContinuousPath.finiteEvaluation (q k) path) ∂K x) =
        fun k ↦ ∫ y, f y ∂Lseq k x :=
    funext heq
  rw [hsame] at hpath
  have hlimit := tendsto_nhds_unique hpath (hfinite x f)
  have heval : Measurable (ContinuousPath.finiteEvaluation (α := α) τ) :=
    ContinuousPath.measurable_finiteEvaluation τ
  have hmap :
      (K.map (ContinuousPath.finiteEvaluation τ)) x =
        (K x).map (ContinuousPath.finiteEvaluation τ) :=
    Kernel.map_apply K heval x
  rw [hmap, integral_map]
  · exact hlimit
  · exact heval.aemeasurable
  · exact f.continuous.aestronglyMeasurable
