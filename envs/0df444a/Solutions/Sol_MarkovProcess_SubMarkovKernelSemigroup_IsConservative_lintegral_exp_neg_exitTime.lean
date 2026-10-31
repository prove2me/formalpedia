-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.lintegral_exp_neg_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:37:47.158819+00:00
-- url     : https://prove2.me/submissions/a2904ceb-4ca5-4a94-ae28-88aa328fc3cb

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
import Theorems.Thm_MarkovProcess_ContinuousPath_survivalSet_ne_top
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedResolvent_eq_lintegral

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

/-- The survival set below an infinite extended horizon is the positive half-line. -/
theorem survivalSet_top :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} ∩ Set.Ioi 0 = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
  exact and_iff_right ENNReal.coe_lt_top



/-- The time set on which the nonnegative-time coordinate remains below an extended horizon. -/
theorem survivalSet (tau : ℝ≥0∞) :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0 =
      if tau = ⊤ then Set.Ioi 0 else Set.Ioo 0 tau.toReal := by
  by_cases htau : tau = ⊤
  · rw [if_pos htau, htau]
    exact survivalSet_top
  · rw [if_neg htau]
    exact survivalSet_ne_top tau htau

end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order











end Order

section WithTopValue











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

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

/-- The integral of a decaying exponential over a finite interval. -/
private theorem integral_exp_neg_mul_Ioc_zero (lam : ℝ) (hlam : 0 < lam) (A : ℝ)
    (hA : 0 ≤ A) :
    ∫ t in Set.Ioc (0 : ℝ) A, Real.exp (-lam * t) =
      (1 - Real.exp (-lam * A)) / lam := by
  rw [← intervalIntegral.integral_of_le hA]
  have hn : -lam ≠ 0 := neg_ne_zero.mpr hlam.ne'
  have h := intervalIntegral.integral_comp_mul_left
    (f := Real.exp) (a := 0) (b := A) hn
  rw [mul_zero, integral_exp] at h
  rw [show (fun t : ℝ ↦ Real.exp (-lam * t)) =
      fun t ↦ Real.exp ((-lam) * t) by funext t; rw [neg_mul], h]
  simp only [smul_eq_mul, Real.exp_zero]
  field_simp
  ring

/-- The improper integral of a decaying exponential on the positive half-line. -/
private theorem integral_exp_neg_mul_Ioi_zero (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) = lam⁻¹ :=
  Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam

/-- The `ℝ≥0∞` integral of a decaying exponential over a finite interval. -/
private theorem lintegral_exp_neg_mul_Ioc_zero (lam : ℝ) (hlam : 0 < lam) (A : ℝ)
    (hA : 0 ≤ A) :
    ∫⁻ t in Set.Ioc (0 : ℝ) A, ENNReal.ofReal (Real.exp (-lam * t)) =
      ENNReal.ofReal ((1 - Real.exp (-lam * A)) / lam) := by
  rw [← integral_exp_neg_mul_Ioc_zero lam hlam A hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).integrableOn_Ioc)
    (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)).symm

/-- The `ℝ≥0∞` integral of a decaying exponential on the positive half-line. -/
private theorem lintegral_exp_neg_mul_Ioi_zero (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) =
      ENNReal.ofReal lam⁻¹ := by
  rw [← integral_exp_neg_mul_Ioi_zero lam hlam]
  exact (ofReal_integral_eq_lintegral_ofReal
    (exp_neg_integrableOn_Ioi 0 hlam)
    (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)).symm

/-- Multiplying the discounted occupation time below an extended horizon by the discount rate
gives one minus the discounted terminal weight, with the latter set to zero at infinity. -/
private theorem ofReal_mul_lintegral_exp_neg_mul_indicator (lam : ℝ) (hlam : 0 < lam)
    (tau : ℝ≥0∞) :
    ENNReal.ofReal lam *
        (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator 1 t) =
      1 - ({tau | tau < ⊤} : Set ℝ≥0∞).indicator
        (fun tau ↦ ENNReal.ofReal (Real.exp (-lam * tau.toReal))) tau := by
  let S : Set ℝ := {t | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}
  have hS : MeasurableSet S := measurableSet_lt
    (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
  have hfun : (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-lam * t)) * S.indicator 1 t) =
      S.indicator (fun t ↦ ENNReal.ofReal (Real.exp (-lam * t))) := by
    funext t
    by_cases ht : t ∈ S
    · simp only [neg_mul, Set.indicator_of_mem ht, Pi.one_apply, mul_one]
    · simp only [neg_mul, Set.indicator_of_notMem ht, mul_zero]
  rw [hfun, setLIntegral_indicator hS]
  by_cases htau : tau = ⊤
  · rw [ContinuousPath.survivalSet tau, if_pos htau,
      lintegral_exp_neg_mul_Ioi_zero lam hlam]
    subst tau
    have hnot : (⊤ : ℝ≥0∞) ∉ {tau | tau < ⊤} := by
      simp only [mem_ofPred_eq, lt_self_iff_false, not_false_eq_true]
    rw [Set.indicator_of_notMem hnot, tsub_zero]
    rw [← ENNReal.ofReal_mul hlam.le]
    simp only [mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]
  · rw [ContinuousPath.survivalSet tau, if_neg htau]
    rw [show volume.restrict (Set.Ioo (0 : ℝ) tau.toReal) =
        volume.restrict (Set.Ioc 0 tau.toReal) from
      Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [lintegral_exp_neg_mul_Ioc_zero lam hlam tau.toReal ENNReal.toReal_nonneg]
    have hmem : tau ∈ {tau | tau < ⊤} := lt_top_iff_ne_top.mpr htau
    rw [Set.indicator_of_mem hmem]
    rw [← ENNReal.ofReal_mul hlam.le, mul_div_cancel₀ _ hlam.ne',
      ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed resolvent of one is the expected discounted occupation time before exit. -/
private theorem killedResolvent_one_eq_lintegral (lam : ℝ) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) x =
      ∫⁻ omega, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime U omega}.indicator 1 t)
        ∂(IsConservative.continuousProcess P hP x) := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP U hU lam measurable_const x]
  refine lintegral_congr fun omega ↦ ?_
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp only [Set.indicator_apply, Pi.one_apply]





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
theorem solution (lam : ℝ) (hlam : 0 < lam) (x : alpha) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
        ∂(IsConservative.continuousProcess P hP x) =
      1 - ENNReal.ofReal lam *
        IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) x := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let S : Set (ContinuousPath alpha) :=
    {omega | ContinuousPath.exitTime U omega < ⊤}
  let W : ContinuousPath alpha → ℝ≥0∞ := S.indicator fun omega ↦
    ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))
  let H : ContinuousPath alpha → ℝ≥0∞ := fun omega ↦
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
        ContinuousPath.exitTime U omega}.indicator 1 t
  have hExit : Measurable fun omega : ContinuousPath alpha ↦ ContinuousPath.exitTime U omega :=
    ContinuousPath.measurable_exitTime U hU
  have hS : MeasurableSet S := measurableSet_lt hExit measurable_const
  have hW : Measurable W := by
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (ENNReal.measurable_toReal.comp hExit)))).indicator hS
  have hJoint : Measurable (fun p : ℝ × ContinuousPath alpha ↦
      ENNReal.ofReal (Real.exp (-lam * p.1)) *
        {p : ℝ × ContinuousPath alpha |
          ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime U p.2}.indicator 1 p) := by
    have hset : MeasurableSet {p : ℝ × ContinuousPath alpha |
        ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2} :=
      measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_fst))
        (hExit.comp measurable_snd)
    exact (ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)).mul (measurable_const.indicator hset)
  have hH : Measurable H := by
    exact hJoint.lintegral_prod_left' (μ := volume.restrict (Set.Ioi 0))
  have hWle : W ≤ fun _ ↦ 1 := by
    intro omega
    by_cases homega : omega ∈ S
    · change S.indicator (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega ≤ 1
      rw [Set.indicator_of_mem homega]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((Real.exp_le_one_iff).mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam.le) ENNReal.toReal_nonneg))
    · change S.indicator (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega ≤ 1
      rw [Set.indicator_of_notMem homega]
      exact zero_le
  have hWint : ∫⁻ omega, W omega ∂Q ≤ 1 := by
    calc
      ∫⁻ omega, W omega ∂Q ≤ ∫⁻ _omega, 1 ∂Q := lintegral_mono hWle
      _ = 1 := by simp only [lintegral_one, measure_univ]
  have hWtop : ∫⁻ omega, W omega ∂Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hWint
  have hSub : ∫⁻ omega, 1 - W omega ∂Q = 1 - ∫⁻ omega, W omega ∂Q := by
    rw [lintegral_sub hW hWtop (Eventually.of_forall hWle)]
    simp only [lintegral_one, measure_univ]
  change ∫⁻ omega, W omega ∂Q =
    1 - ENNReal.ofReal lam * IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) x
  rw [killedResolvent_one_eq_lintegral P hP U hU lam x]
  change ∫⁻ omega, W omega ∂Q = 1 - ENNReal.ofReal lam * ∫⁻ omega, H omega ∂Q
  rw [← lintegral_const_mul _ hH]
  have hKey : (fun omega ↦ ENNReal.ofReal lam * H omega) = fun omega ↦ 1 - W omega := by
    funext omega
    exact ofReal_mul_lintegral_exp_neg_mul_indicator lam hlam
      (ContinuousPath.exitTime U omega)
  rw [hKey, hSub]
  exact (ENNReal.sub_sub_cancel ENNReal.one_ne_top hWint).symm
