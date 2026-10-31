-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.iSup_eq_of_tendsto_nhdsGT_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:23:05.167665+00:00
-- url     : https://prove2.me/submissions/f730b2a0-02e6-4325-b611-810ba40c6f66

import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The killed resolvent

The resolvent of the process killed at the exit of an open set `U`, at the shift `λ > 0`, is the
Laplace transform of the killed kernels,

  `killedResolvent λ f x = ∫ t in (0, ∞), e^{-λ t} (∫ f d(killedKernel t x)) dt`,

and this file proves the path-space formula

  `killedResolvent λ f x = E_x ∫_0^{τ_U} e^{-λ t} f(ω_t) dt`

(`killedResolvent_eq_lintegral`), for nonnegative extended measurable `f`; the integral over time
runs up to the exit time, where the survival indicator vanishes. The statement is an identity of
`ℝ≥0∞`-valued integrals, proved by Tonelli's theorem, so it carries no integrability hypothesis;
a consumer working with real-valued bounded `f` splits it into its positive and negative parts.

This is the probabilistic side of the Dirichlet resolvent `(λ − L)⁻¹` on `U` with zero boundary
values: the identification with the analytic resolvent of a given operator is the consumer's
statement about that operator.  One order fact is recorded alongside: the killed resolvent is
antitone in the shift (`IsConservative.killedResolvent_antitone`), because a larger shift
discounts the future more.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)







/-- **The killed resolvent is antitone in the shift.**  A larger shift discounts the future more,
so it produces a smaller resolvent. -/
theorem IsConservative.killedResolvent_antitone (f : alpha → ℝ≥0∞) (x : alpha) {lam mu : ℝ}
    (hle : lam ≤ mu) :
    IsConservative.killedResolvent P hP U hU mu f x ≤
      IsConservative.killedResolvent P hP U hU lam f x := by
  unfold IsConservative.killedResolvent
  refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_)
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) _
  exact mul_le_mul_of_nonneg_right (neg_le_neg hle) (le_of_lt ht)

end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying the expected exit time with a Dirichlet resolvent

The killed resolvent of the constant function one at the shift zero is the expected exit time,

  `E_x τ_U = R^U_0 1 (x)`  (`IsConservative.lintegral_exitTime_eq_killedResolvent_zero`),

and the shift zero is the increasing limit of the positive shifts `1 / (n + 1)`
(`IsConservative.killedResolvent_zero_eq_iSup`).  Both statements are unconditional.

Consumers who identify the killed resolvent at positive shifts with an analytically defined
Dirichlet resolvent `RU` then read the expected exit time off the limit of `RU`
(`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq`): the identification enters only as a
hypothesis, so nothing here depends on how it is established.  Two one-sided corollaries are
recorded, an upper bound from a uniform upper bound on the limit
(`IsConservative.lintegral_exitTime_le_of_killedResolvent_eq`) and a lower bound on a subset from a
uniform lower bound there (`IsConservative.le_lintegral_exitTime_of_killedResolvent_eq`).

The limit of `RU` enters those statements as a supremum along the shifts `1 / (n + 1)`.  A
consumer who instead has a limit as the shift decreases to zero converts it with
`IsConservative.iSup_eq_of_tendsto_nhdsGT_zero`: the killed resolvent is antitone in the shift, so
the identification makes `RU` antitone on `U` too and the sequence increases to its limit.

The consumer-supplied resolvent and its limit are `ℝ≥0∞`-valued, so no integrability or finiteness
hypothesis appears; a consumer working with real-valued solutions bridges with `ENNReal.ofReal`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)









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
# Identifying the expected exit time with a Dirichlet resolvent

The killed resolvent of the constant function one at the shift zero is the expected exit time,

  `E_x τ_U = R^U_0 1 (x)`  (`IsConservative.lintegral_exitTime_eq_killedResolvent_zero`),

and the shift zero is the increasing limit of the positive shifts `1 / (n + 1)`
(`IsConservative.killedResolvent_zero_eq_iSup`).  Both statements are unconditional.

Consumers who identify the killed resolvent at positive shifts with an analytically defined
Dirichlet resolvent `RU` then read the expected exit time off the limit of `RU`
(`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq`): the identification enters only as a
hypothesis, so nothing here depends on how it is established.  Two one-sided corollaries are
recorded, an upper bound from a uniform upper bound on the limit
(`IsConservative.lintegral_exitTime_le_of_killedResolvent_eq`) and a lower bound on a subset from a
uniform lower bound there (`IsConservative.le_lintegral_exitTime_of_killedResolvent_eq`).

The limit of `RU` enters those statements as a supremum along the shifts `1 / (n + 1)`.  A
consumer who instead has a limit as the shift decreases to zero converts it with
`IsConservative.iSup_eq_of_tendsto_nhdsGT_zero`: the killed resolvent is antitone in the shift, so
the identification makes `RU` antitone on `U` too and the sequence increases to its limit.

The consumer-supplied resolvent and its limit are `ℝ≥0∞`-valued, so no integrability or finiteness
hypothesis appears; a consumer working with real-valued solutions bridges with `ENNReal.ofReal`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (U : Set alpha) (hU : IsOpen U)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hw : ∀ y ∈ U, Tendsto (fun lam : ℝ ↦ RU lam y) (𝓝[>] (0 : ℝ)) (𝓝 (w y))) :
    ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y := by
  intro y hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n ↦ by positivity
  have hmono : Monotone fun n : ℕ ↦ RU ((n : ℝ) + 1)⁻¹ y := by
    intro m n hmn
    dsimp only
    rw [← hident _ (hpos m) y hy, ← hident _ (hpos n) y hy]
    refine IsConservative.killedResolvent_antitone P hP U hU (fun _ ↦ 1) y ?_
    exact inv_anti₀ (by positivity) (add_le_add (Nat.cast_le.mpr hmn) le_rfl)
  have hseq : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall fun n ↦ hpos n)
    have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [one_div] using h
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) ((hw y hy).comp hseq)
