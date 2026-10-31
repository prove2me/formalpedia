-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.onePointKernelSemigroup_apply_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:58.257523+00:00
-- url     : https://prove2.me/submissions/b25568c5-4c24-4e0e-b77e-0e4dcb44c232

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
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
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_onePointSemigroupAction_coe

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]





variable [LocallyCompactSpace alpha]







end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

































end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty




open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]







namespace MarkovProcess.PositiveC0ContractiveResolvent

end MarkovProcess.PositiveC0ContractiveResolvent
open MarkovProcess.PositiveC0ContractiveResolvent
theorem solution
    (R : PositiveC0ContractiveResolvent X) (t : NNReal) (x : X) :
    R.onePointKernelSemigroup t (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) +
        (1 - R.kernelSemigroup t x Set.univ) • Measure.dirac OnePoint.infty := by
  let : (R.kernelSemigroup t x).Regular := by
    rw [PositiveC0ContractiveResolvent.kernelSemigroup,
      PositiveC0SemigroupKernel.kernelSemigroup_apply,
      PositiveC0OperatorKernel.kernel_apply]
    infer_instance
  let : IsFiniteMeasure (R.kernelSemigroup t x) :=
    ⟨lt_of_le_of_lt (R.kernelSemigroup.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  let : Measure.InnerRegularCompactLTTop
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) :=
    Measure.InnerRegularCompactLTTop.map_of_continuous OnePoint.continuous_coe
  let : IsFiniteMeasure
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) := inferInstance
  have hmissing_ne_top : 1 - R.kernelSemigroup t x Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  let : IsFiniteMeasure
      ((1 - R.kernelSemigroup t x Set.univ) •
        Measure.dirac (OnePoint.infty : OnePoint X)) :=
    Measure.smul_finite _ hmissing_ne_top
  let : IsFiniteMeasure
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X) +
        (1 - R.kernelSemigroup t x Set.univ) • Measure.dirac OnePoint.infty) :=
    ⟨(ENNReal.add_lt_top).2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩⟩
  let : (R.onePointKernelSemigroup t (x : OnePoint X)).Regular := by
    rw [onePointKernelSemigroup, PositiveC0ContractiveResolvent.kernelSemigroup,
      PositiveC0SemigroupKernel.kernelSemigroup_apply,
      PositiveC0OperatorKernel.kernel_apply]
    infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : C₀(OnePoint X, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hmain := R.integral_onePointKernelSemigroup t g (x : OnePoint X)
  rw [onePointSemigroup_apply, R.onePointSemigroupAction_coe] at hmain
  have hmap :
      ∫ z, f z ∂(R.kernelSemigroup t x).map ((↑) : X → OnePoint X) =
        ∫ y, f (y : OnePoint X) ∂R.kernelSemigroup t x := by
    simpa only using! integral_map OnePoint.continuous_coe.aemeasurable
      f.continuous.aestronglyMeasurable
  have hmass : R.kernelSemigroup t x Set.univ ≠ ⊤ :=
    (lt_of_le_of_lt (R.kernelSemigroup.measure_univ_le_one t x) ENNReal.one_lt_top).ne
  have hmissing :
      (1 - R.kernelSemigroup t x Set.univ).toReal =
        1 - (R.kernelSemigroup t x).real Set.univ := by
    rw [ENNReal.toReal_sub_of_le (R.kernelSemigroup.measure_univ_le_one t x)
        ENNReal.one_ne_top,
      ENNReal.toReal_one, measureReal_def]
  have hleft : ∫ z, f z ∂R.onePointKernelSemigroup t (x : OnePoint X) =
      ∫ z, g z ∂R.onePointKernelSemigroup t (x : OnePoint X) := by
    apply integral_congr_ae
    filter_upwards with z
    exact (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f z).symm
  rw [integral_add_measure]
  · rw [hleft, hmain, hmap, integral_smul_measure, integral_dirac, hmissing, smul_eq_mul]
    congr 2
  · exact f.integrable
  · exact f.integrable
