-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.lintegral_exitTime_le_of_killedResolvent_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:53:03.271746+00:00
-- url     : https://prove2.me/submissions/aa46eebd-cdf9-41ca-88ff-33c58ac59541

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedResolvent_zero_eq_iSup
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_lintegral_exitTime_eq_killedResolvent_zero

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)



/-- **The expected exit time from an identified Dirichlet resolvent.**  If the killed resolvent of
one agrees on `U` with a consumer-supplied family `RU` at every positive shift, and `RU` has the
pointwise limit `w` along the shifts `1 / (n + 1)`, then the expected exit time is `w`. -/
theorem IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq (U : Set alpha) (hU : IsOpen U)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hlim : ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y)
    {x : alpha} (hx : x ∈ U) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) = w x := by
  rw [IsConservative.lintegral_exitTime_eq_killedResolvent_zero P hP U hU x,
    IsConservative.killedResolvent_zero_eq_iSup P hP U hU measurable_const x, ← hlim x hx]
  refine iSup_congr fun n ↦ ?_
  exact hident _ (by positivity) x hx





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
    (hlim : ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y)
    (M : ℝ≥0∞) (hupper : ∀ y ∈ U, w y ≤ M) {x : alpha} (hx : x ∈ U) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) ≤ M := by
  rw [IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq P hP RU w U hU hident hlim hx]
  exact hupper x hx
