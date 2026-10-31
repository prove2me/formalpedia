-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.measure_exitTime_le_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:31:51.79399+00:00
-- url     : https://prove2.me/submissions/a7a55602-fb94-4504-8e8d-a88273fd4762

import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Integral.ExpDecay
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
# The Laplace transform of an exit time

For the continuous-path process of a conservative semigroup, this file identifies the Laplace
transform of the finite exit time from an open set with one minus the killed resolvent of the
constant function one.  It also gives the resulting Chernoff bound on the early-exit event
`{exitTime U ≤ t}`.

Main results: `IsConservative.lintegral_exp_neg_exitTime` and
`IsConservative.measure_exitTime_le_le`.

No moment bound or almost-sure finiteness of the exit time is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section











variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)







end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The Laplace transform of an exit time

For the continuous-path process of a conservative semigroup, this file identifies the Laplace
transform of the finite exit time from an open set with one minus the killed resolvent of the
constant function one.  It also gives the resulting Chernoff bound on the early-exit event
`{exitTime U ≤ t}`.

Main results: `IsConservative.lintegral_exp_neg_exitTime` and
`IsConservative.measure_exitTime_le_le`.

No moment bound or almost-sure finiteness of the exit time is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal













variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)





namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative
end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
include hU in

theorem solution (lam : ℝ) (hlam : 0 ≤ lam)
    (t : NNReal) (x : alpha) :
    IsConservative.continuousProcess P hP x
        {omega | ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * (t : ℝ))) *
        ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦ ENNReal.ofReal
            (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
          ∂(IsConservative.continuousProcess P hP x) := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let A : Set (ContinuousPath alpha) :=
    {omega | ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞)}
  let S : Set (ContinuousPath alpha) :=
    {omega | ContinuousPath.exitTime U omega < ⊤}
  let W : ContinuousPath alpha → ℝ≥0∞ := S.indicator fun omega ↦
    ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  have hA : MeasurableSet A := measurableSet_le hExit measurable_const
  have hS : MeasurableSet S := measurableSet_lt hExit measurable_const
  have hW : Measurable W := by
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (ENNReal.measurable_toReal.comp hExit)))).indicator hS
  change Q A ≤ ENNReal.ofReal (Real.exp (lam * (t : ℝ))) * ∫⁻ omega, W omega ∂Q
  rw [← lintegral_indicator_one hA, ← lintegral_const_mul _ hW]
  refine lintegral_mono fun omega ↦ ?_
  by_cases homega : omega ∈ A
  · rw [Set.indicator_of_mem homega]
    have htauTop : ContinuousPath.exitTime U omega ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top homega
    have homegaS : omega ∈ S := lt_top_iff_ne_top.mpr htauTop
    change 1 ≤ ENNReal.ofReal (Real.exp (lam * (t : ℝ))) *
      S.indicator (fun omega ↦ ENNReal.ofReal
        (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
    rw [Set.indicator_of_mem homegaS, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
    have htau : (ContinuousPath.exitTime U omega).toReal ≤ (t : ℝ) := by
      exact (ENNReal.toReal_le_toReal htauTop ENNReal.coe_ne_top).mpr homega
    calc
      0 ≤ lam * ((t : ℝ) - (ContinuousPath.exitTime U omega).toReal) :=
        mul_nonneg hlam (sub_nonneg.mpr htau)
      _ = lam * (t : ℝ) + -lam * (ContinuousPath.exitTime U omega).toReal := by ring
  · rw [Set.indicator_of_notMem homega]
    exact zero_le
