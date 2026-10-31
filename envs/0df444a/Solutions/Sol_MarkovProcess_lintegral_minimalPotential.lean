-- Prove2me | solution 1 for MarkovProcess.lintegral_minimalPotential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:29:51.844705+00:00
-- url     : https://prove2.me/submissions/3885ca64-ce80-4f10-a374-f7887a28c3ff

import Definitions.Def_MarkovProcess_V3H_Killed_GluingLinearity_fff8f190
import Definitions.Def_MarkovProcess_V3H_Killed_GluingMeasure_1a481231
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
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The potential measure of the supremum resolvent

Additivity and continuity along monotone limits make the supremum resolvent countably additive
on measurable observables (`minimalResolvent_tsum`), so at a positive shift it is the integral
against a finite measure on the state space, the potential measure `minimalPotential`
(`lintegral_minimalPotential`, `isFiniteMeasure_minimalPotential`).

This is the form in which the supremum resolvent is compared with the kernel resolvent of a
transition semigroup: an identity tested on continuous observables vanishing at infinity extends
to all nonnegative measurable observables through the two potential measures.

Monotonicity of the transported resolvents in the index is a bare hypothesis throughout.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)







/-- The potential measure of a measurable set is the supremum resolvent of its indicator. -/
theorem minimalPotential_apply (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) {S : Set alpha} (hS : MeasurableSet S) :
    minimalPotential R emb hemb hmono hlam x S =
      minimalResolvent R emb lam (S.indicator fun _ ↦ 1) x :=
  Measure.ofMeasurable_apply S hS





end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The potential measure of the supremum resolvent

Additivity and continuity along monotone limits make the supremum resolvent countably additive
on measurable observables (`minimalResolvent_tsum`), so at a positive shift it is the integral
against a finite measure on the state space, the potential measure `minimalPotential`
(`lintegral_minimalPotential`, `isFiniteMeasure_minimalPotential`).

This is the form in which the supremum resolvent is compared with the kernel resolvent of a
transition semigroup: an identity tested on continuous observables vanishing at infinity extends
to all nonnegative measurable observables through the two potential measures.

Monotonicity of the transported resolvents in the index is a bare hypothesis throughout.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)









namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂minimalPotential R emb hemb hmono hlam x = minimalResolvent R emb lam f x := by
  refine Measurable.ennreal_induction
    (motive := fun g ↦ ∫⁻ y, g y ∂minimalPotential R emb hemb hmono hlam x =
      minimalResolvent R emb lam g x) ?_ ?_ ?_ hf
  · intro c S hS
    have hconst : (S.indicator fun _ ↦ c) = fun y ↦ c * (S.indicator fun _ ↦ (1 : ℝ≥0∞)) y := by
      funext y
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
    rw [lintegral_indicator_const hS, minimalPotential_apply R emb hemb hmono hlam x hS,
      hconst, minimalResolvent_const_mul R emb hemb lam c
        (measurable_const.indicator hS) x]
  · intro g h _hdisj hg hh ihg ihh
    have hlhs : ∫⁻ y, (g + h) y ∂minimalPotential R emb hemb hmono hlam x =
        ∫⁻ y, g y ∂minimalPotential R emb hemb hmono hlam x +
          ∫⁻ y, h y ∂minimalPotential R emb hemb hmono hlam x := by
      simp only [Pi.add_apply]
      exact lintegral_add_left hg _
    rw [hlhs, ihg, ihh]
    exact (minimalResolvent_add R emb hemb hmono hlam hg hh x).symm
  · intro g hg hgmono ih
    rw [lintegral_iSup hg hgmono, minimalResolvent_iSup R emb hemb lam hg hgmono x]
    exact iSup_congr ih
