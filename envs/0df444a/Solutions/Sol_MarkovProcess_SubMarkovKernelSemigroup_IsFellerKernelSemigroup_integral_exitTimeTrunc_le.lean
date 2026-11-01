-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.integral_exitTimeTrunc_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:34:28.374254+00:00
-- url     : https://prove2.me/submissions/0c45c877-c42a-4be1-92ff-067bb1507e1d

import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_integrable_integral_generator_stoppingTime
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
# Dynkin's formula at a bounded stopping time, and the expected exit time

The Dynkin process of `f` in the generator domain is a martingale for the canonical filtration
under the continuous-path process `Q = continuousProcess P hP` (`martingale_dynkinProcess`), it is
bounded on bounded time intervals, and it is continuous in time along every path.  Optional
stopping (`MarkovProcess.integral_stoppedValue_eq_of_locallyBounded`) therefore applies at every
finite stopping time `T` bounded by a deterministic horizon, and gives **Dynkin's formula at a
bounded stopping time**:

  `E_x f(omega (T omega)) - f x = E_x ∫₀^{T omega} (L f)(omega s) ds`

(`integral_eval_stoppingTime_sub_eq_integral_integral_generator`, with the equivalent compact form
`integral_dynkinProcess_stoppingTime`).

The classical consequence is the **expected exit time bound**: if `L f ≤ -1` on an open set `U`
and `f` is bounded below by `m`, then the exit time from `U`, truncated at any horizon `K`, has
expectation at most `f x - m` from every starting point `x`
(`integral_exitTimeTrunc_le`).  The proof uses that strictly before the exit time the path is
still inside `U`, so the integrand of Dynkin's formula is at most `-1` there.

The truncation at `K` is what keeps the stopping time finite; the bound is uniform in `K`, and
`Trajectory/ExpectedExitTime.lean` removes the truncation by monotone convergence
(`lintegral_exitTime_le`, `ae_exitTime_lt_top`).

The progressive-measurability and optional-stopping statements below are the zero-discount
specializations of the corresponding results in `Trajectory/DiscountedDynkin.lean`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProgressiveMeasurability

variable [SecondCountableTopology alpha]





end ProgressiveMeasurability

section Stopping

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)



/-- The position at a finite stopping time is integrable: it is Borel measurable and bounded by
the `C₀` norm of `f`. -/
theorem IsFellerKernelSemigroup.integrable_eval_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) (x : alpha) :
    Integrable (fun omega : ContinuousPath alpha ↦ (f : C₀(alpha, ℝ)) (omega (T omega)))
      (IsConservative.continuousProcess P hP x) := by
  refine Integrable.of_bound
    (((f : C₀(alpha, ℝ)).continuous.measurable.comp
      (ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable)
    ‖(f : C₀(alpha, ℝ))‖ (Eventually.of_forall fun omega ↦ ?_)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm (f : C₀(alpha, ℝ)).toBCF _





end Stopping

section ExitTime

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)

omit [MeasurableSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha] [CompleteSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] in
/-- Strictly before the truncated exit time, the path is still inside the open set `U`. -/
private theorem mem_of_lt_exitTimeTrunc (U : Set alpha) (K : NNReal)
    (omega : ContinuousPath alpha) (t : NNReal) (ht : t < ContinuousPath.exitTimeTrunc U K omega) :
    omega t ∈ U := by
  have hlt : ((t : NNReal) : ℝ≥0∞) <
      ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr ht
  have hle : ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) ≤
      ContinuousPath.exitTime U omega := by
    have h : ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : WithTop NNReal) ≤
        ContinuousPath.exitTimeTop U omega := by
      rw [ContinuousPath.coe_exitTimeTrunc]
      exact min_le_left _ _
    exact h
  exact ContinuousPath.mem_of_lt_exitTime U omega t (hlt.trans_le hle)

omit [LocallyCompactSpace alpha] in
/-- The truncated exit time is integrable: it is Borel measurable and bounded by its horizon. -/
private theorem integrable_exitTimeTrunc (U : Set alpha) (hU : IsOpen U) (K : NNReal)
    (x : alpha) :
    Integrable (fun omega : ContinuousPath alpha ↦
        ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ))
      (IsConservative.continuousProcess P hP x) := by
  have hmeas : Measurable (ContinuousPath.exitTimeTrunc U K : ContinuousPath alpha → NNReal) :=
    ContinuousPath.measurable_of_isStoppingTime _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)
  refine Integrable.of_bound (NNReal.continuous_coe.measurable.comp hmeas).aestronglyMeasurable
    (K : ℝ) (Eventually.of_forall fun omega ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (ContinuousPath.exitTimeTrunc U K omega).coe_nonneg]
  exact NNReal.coe_le_coe.mpr (ContinuousPath.exitTimeTrunc_le U K omega)

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
/-- Along a path, the Dynkin integrand is at most `-1` almost everywhere on `[0, T]`, where `T`
is the truncated exit time: strictly before `T` the path is inside `U`, and the endpoint is a
null set. -/
private theorem integral_generator_exitTimeTrunc_le (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1) (K : NNReal)
    (omega : ContinuousPath alpha) :
    (∫ s in (0 : ℝ)..((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))) ≤
      -((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ) := by
  have hb0 : (0 : ℝ) ≤ ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ) :=
    (ContinuousPath.exitTimeTrunc U K omega).coe_nonneg
  have hcont : Continuous fun s : ℝ ↦
      (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) :=
    (hFeller.c0Semigroup.generator f).continuous.comp
      (omega.continuous.comp continuous_real_toNNReal)
  have hsingleton : ∀ᵐ s : ℝ ∂(volume : Measure ℝ),
      s ≠ ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ) := by
    rw [ae_iff]
    simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
  have hae : ∀ᵐ s : ℝ ∂(volume.restrict
      (Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ))),
      (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) ≤ -1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hsingleton] with s hs hsmem
    refine hLf _ (mem_of_lt_exitTimeTrunc U K omega (Real.toNNReal s) ?_)
    exact (Real.toNNReal_lt_iff_lt_coe hsmem.1).mpr (lt_of_le_of_ne hsmem.2 hs)
  have hmono := intervalIntegral.integral_mono_ae_restrict hb0
    (hcont.intervalIntegrable _ _) (intervalIntegrable_const (c := (-1 : ℝ))) hae
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  linarith only [hmono]



end ExitTime

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
# Dynkin's formula at a bounded stopping time, and the expected exit time

The Dynkin process of `f` in the generator domain is a martingale for the canonical filtration
under the continuous-path process `Q = continuousProcess P hP` (`martingale_dynkinProcess`), it is
bounded on bounded time intervals, and it is continuous in time along every path.  Optional
stopping (`MarkovProcess.integral_stoppedValue_eq_of_locallyBounded`) therefore applies at every
finite stopping time `T` bounded by a deterministic horizon, and gives **Dynkin's formula at a
bounded stopping time**:

  `E_x f(omega (T omega)) - f x = E_x ∫₀^{T omega} (L f)(omega s) ds`

(`integral_eval_stoppingTime_sub_eq_integral_integral_generator`, with the equivalent compact form
`integral_dynkinProcess_stoppingTime`).

The classical consequence is the **expected exit time bound**: if `L f ≤ -1` on an open set `U`
and `f` is bounded below by `m`, then the exit time from `U`, truncated at any horizon `K`, has
expectation at most `f x - m` from every starting point `x`
(`integral_exitTimeTrunc_le`).  The proof uses that strictly before the exit time the path is
still inside `U`, so the integrand of Dynkin's formula is at most `-1` there.

The truncation at `K` is what keeps the stopping time finite; the bound is uniform in `K`, and
`Trajectory/ExpectedExitTime.lean` removes the truncation by monotone convergence
(`lintegral_exitTime_le`, `ae_exitTime_lt_top`).

The progressive-measurability and optional-stopping statements below are the zero-discount
specializations of the corresponding results in `Trajectory/DiscountedDynkin.lean`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}




variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)







namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1)
    {m : ℝ} (hm : ∀ y, m ≤ (f : C₀(alpha, ℝ)) y) (K : NNReal) (x : alpha) :
    ∫ omega, ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x) ≤ (f : C₀(alpha, ℝ)) x - m := by
  have hT := ContinuousPath.isStoppingTime_exitTimeTrunc U hU K
  have hTK := ContinuousPath.exitTimeTrunc_le U K
  have hdynkin := hFeller.integral_eval_stoppingTime_sub_eq_integral_integral_generator hP hK f
    (ContinuousPath.exitTimeTrunc U K) hT hTK x
  have hlow : m ≤ ∫ omega, (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
      ∂(IsConservative.continuousProcess P hP x) := by
    have hconst : ∫ _omega : ContinuousPath alpha, m
        ∂(IsConservative.continuousProcess P hP x) = m := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← hconst]
    exact integral_mono (integrable_const m)
      (hFeller.integrable_eval_stoppingTime hP f _ hT x) fun omega ↦ hm _
  have hupper : (∫ omega, (∫ s in (0 : ℝ)..((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      ∂(IsConservative.continuousProcess P hP x)) ≤
      ∫ omega, -((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x) :=
    integral_mono (hFeller.integrable_integral_generator_stoppingTime hP f _ hT hTK x)
      (integrable_exitTimeTrunc hP U hU K x).neg
      fun omega ↦ integral_generator_exitTimeTrunc_le hFeller f U hLf K omega
  rw [integral_neg] at hupper
  linarith only [hdynkin, hlow, hupper]
