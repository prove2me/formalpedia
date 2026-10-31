-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.ae_eq_const_of_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:19:24.095982+00:00
-- url     : https://prove2.me/submissions/8a1faa88-6022-476d-a57b-86a942981cb4

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
open MarkovProcess.SubMarkovKernelSemigroup
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



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hK : P.KolmogorovRegular hP) (a : alpha)
    (hAbsorb : ∀ t, P t a = Measure.dirac a) :
    (fun omega : ContinuousPath alpha ↦ omega) =ᵐ[IsConservative.continuousProcess P hP a]
      fun _ ↦ ContinuousMap.const NNReal a := by
  let mu := IsConservative.continuousProcess P hP a
  have hcoord : ∀ q : DenseTime, ∀ᵐ omega ∂mu,
      omega (DenseTime.castOrderEmbedding q) = a := by
    intro q
    have hmeas : Measurable
        (fun omega : ContinuousPath alpha ↦ omega (DenseTime.castOrderEmbedding q)) :=
      ContinuousPath.measurable_coordinateProcess (alpha := alpha) _
    have hmap := IsConservative.continuousProcess_map_eval P hP hK q
    have hmapa : Measure.map (fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) mu = Measure.dirac a := by
      rw [show mu = IsConservative.continuousProcess P hP a by rfl,
        ← Kernel.map_apply _ hmeas, hmap, hAbsorb]
    have hsingleton : MeasurableSet ({a}ᶜ : Set alpha) :=
      (isClosed_singleton (x := a)).measurableSet.compl
    have hzero : mu ((fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) ⁻¹' ({a}ᶜ : Set alpha)) = 0 := by
      rw [← Measure.map_apply hmeas hsingleton, hmapa, Measure.dirac_apply' a hsingleton,
        Set.indicator_of_notMem (by simp)]
    exact hzero
  have hall : ∀ᵐ omega ∂mu, ∀ q : DenseTime,
      omega (DenseTime.castOrderEmbedding q) = a := ae_all_iff.mpr hcoord
  filter_upwards [hall] with omega homega
  apply ContinuousPath.denseRestriction_injective
  funext q
  rw [ContinuousPath.denseRestriction_apply, ContinuousPath.denseRestriction_apply, homega q]
  rfl
