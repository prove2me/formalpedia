-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedResolvent_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:26:05.537779+00:00
-- url     : https://prove2.me/submissions/eb9caae7-84e1-49be-a275-b71e3ad27670

import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
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



/-- An integral against a killed kernel is an integral over the survival event. -/
theorem IsConservative.lintegral_killedKernel (t : NNReal) (x : alpha) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU t x) =
      ∫⁻ omega, {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
        (fun omega ↦ f (omega t)) omega ∂(IsConservative.continuousProcess P hP x) := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  rw [IsConservative.killedKernel_eq_map, lintegral_map hf hmeas,
    ← lintegral_indicator (ContinuousPath.measurableSet_lt_exitTime U hU t)]





end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
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

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal


variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)





namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x =
      ∫⁻ omega, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
            (fun t ↦ f (omega (Real.toNNReal t))) t)
        ∂(IsConservative.continuousProcess P hP x) := by
  have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦ p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet {p : ℝ × ContinuousPath alpha |
      ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_fst))
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
  have hjoint : Measurable (Function.uncurry fun (t : ℝ) (omega : ContinuousPath alpha) ↦
      ENNReal.ofReal (Real.exp (-lam * t)) *
        {omega : ContinuousPath alpha |
          ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
          (fun omega ↦ f (omega (Real.toNNReal t))) omega) := by
    have hrw : (Function.uncurry fun (t : ℝ) (omega : ContinuousPath alpha) ↦
        ENNReal.ofReal (Real.exp (-lam * t)) *
          {omega : ContinuousPath alpha |
            ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
            (fun omega ↦ f (omega (Real.toNNReal t))) omega) =
        fun p : ℝ × ContinuousPath alpha ↦ ENNReal.ofReal (Real.exp (-lam * p.1)) *
          {p : ℝ × ContinuousPath alpha |
            ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2}.indicator
            (fun p ↦ f (p.2 (Real.toNNReal p.1))) p := by
      funext p
      simp only [Function.uncurry, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hrw]
    refine Measurable.mul ?_ ((hf.comp heval).indicator hS)
    exact ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU (Real.toNNReal t) x) =
      ∫⁻ omega, ENNReal.ofReal (Real.exp (-lam * t)) *
        {omega : ContinuousPath alpha |
          ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}.indicator
          (fun omega ↦ f (omega (Real.toNNReal t))) omega ∂(IsConservative.continuousProcess P hP x) := by
    intro t
    have hg : Measurable (fun omega : ContinuousPath alpha ↦ f (omega (Real.toNNReal t))) :=
      hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) _)
    rw [IsConservative.lintegral_killedKernel P hP U hU _ x hf]
    exact (lintegral_const_mul _ (hg.indicator (ContinuousPath.measurableSet_lt_exitTime U hU _))).symm
  unfold IsConservative.killedResolvent
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun omega ↦ ?_
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
