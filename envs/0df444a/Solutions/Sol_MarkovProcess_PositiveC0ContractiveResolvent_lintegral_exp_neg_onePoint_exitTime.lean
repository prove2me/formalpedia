-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.lintegral_exp_neg_onePoint_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:43:33.255916+00:00
-- url     : https://prove2.me/submissions/bfb148e2-a427-40ac-9dbd-be38f0990d52

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
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_killedKernel_onePointLive_eq_map
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_lintegral_exp_neg_exitTime

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
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (lam : ℝ) (hlam : 0 < lam) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    ∫⁻ omega, ({omega | ContinuousPath.exitTime
        (Set.range ((↑) : X → OnePoint X)) omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal (Real.exp (-lam *
          (ContinuousPath.exitTime
            (Set.range ((↑) : X → OnePoint X)) omega).toReal))) omega
      ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X) =
      1 - ENNReal.ofReal lam *
        R.kernelSemigroup.kernelResolvent lam (fun _ : X ↦ 1) x := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  have hUexh : @IsOpen (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (Set.range ((↑) : X → OnePoint X)) :=
    OnePoint.isOpen_range_coe
  have hlem := @IsConservative.lintegral_exp_neg_exitTime (OnePoint X)
    (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact)
    inferInstance OnePoint.instMeasurableSpace inferInstance inferInstance inferInstance
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    (Set.range ((↑) : X → OnePoint X)) hUexh lam hlam
    (x : OnePoint X)
  trans (1 - ENNReal.ofReal lam *
      IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) hUexh lam (fun _ : OnePoint X ↦ 1) x)
  · exact hlem
  congr 2
  unfold IsConservative.killedResolvent SubMarkovKernelSemigroup.kernelResolvent
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  change ENNReal.ofReal (Real.exp (-lam * t)) *
      (∫⁻ _y, 1 ∂IsConservative.killedKernel
        R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe
        (Real.toNNReal t) (x : OnePoint X)) =
    ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ _y, 1 ∂R.kernelSemigroup (Real.toNNReal t) x
  congr 1
  rw [R.killedKernel_onePointLive_eq_map rho hrho_cont hrho_pos hrho_lipschitz hrho_compact hK,
    lintegral_map measurable_const OnePoint.continuous_coe.measurable]
