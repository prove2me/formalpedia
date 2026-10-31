-- Prove2me | solution 1 for MarkovProcess.lintegral_extend_eq_of_forall_zeroAtInfty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:44:27.989043+00:00
-- url     : https://prove2.me/submissions/408707d3-4dab-4ddd-a96c-2482e700dfc4

import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_GluingTransfer_c0e8ad8d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
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
import Theorems.Thm_MarkovProcess_lintegral_extend_eq_lintegral_comap

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# From vanishing observables to measurable ones

An identity between a measure `nu` on a target space and a measure `mu` on a source space,
tested on observables which are supported in the range of a measurable embedding `i` and
extended by zero off it, propagates from continuous observables vanishing at infinity to all
nonnegative measurable observables
(`lintegral_extend_eq_of_forall_zeroAtInfty`).  The reason is that both sides are integrals
against finite Borel measures on the source space, and continuous observables with compact
support already separate finite Borel measures on a locally compact second-countable metric
space.

This is the bridge which upgrades an analytically supplied identity of resolvents, stated for
continuous observables vanishing at infinity, to the identity of the corresponding potential
measures.

No topology on the target space is used, and no relation between the two measures other than the
tested identity is assumed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported

noncomputable section

namespace MarkovProcess

section Topological

variable {X : Type*} [TopologicalSpace X]



/-- A compactly supported function, read as an observable vanishing at infinity, keeps its
values. -/
@[simp] theorem compactlySupportedToZeroAtInfty_apply (f : C_c(X, ℝ)) (x : X) :
    compactlySupportedToZeroAtInfty f x = f x := rfl

end Topological

section Measurable

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]



/-- The pullback of a finite measure along a measurable embedding is finite. -/
theorem isFiniteMeasure_comap {i : X → Y} (hi : MeasurableEmbedding i) (nu : Measure Y)
    [IsFiniteMeasure nu] : IsFiniteMeasure (nu.comap i) := by
  refine ⟨?_⟩
  have hmass : (nu.comap i).map i Set.univ = nu.comap i Set.univ := by
    rw [Measure.map_apply hi.measurable MeasurableSet.univ, Set.preimage_univ]
  rw [← hmass, hi.map_comap]
  exact lt_of_le_of_lt (Measure.restrict_le_self Set.univ) (measure_lt_top nu Set.univ)

end Measurable

section Transfer

variable {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]



end Transfer

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# From vanishing observables to measurable ones

An identity between a measure `nu` on a target space and a measure `mu` on a source space,
tested on observables which are supported in the range of a measurable embedding `i` and
extended by zero off it, propagates from continuous observables vanishing at infinity to all
nonnegative measurable observables
(`lintegral_extend_eq_of_forall_zeroAtInfty`).  The reason is that both sides are integrals
against finite Borel measures on the source space, and continuous observables with compact
support already separate finite Borel measures on a locally compact second-countable metric
space.

This is the bridge which upgrades an analytically supplied identity of resolvents, stated for
continuous observables vanishing at infinity, to the identity of the corresponding potential
measures.

No topology on the target space is used, and no relation between the two measures other than the
tested identity is assumed.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported






variable {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]

namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution {i : X → Y} (hi : MeasurableEmbedding i)
    (nu : Measure Y) (mu : Measure X) [IsFiniteMeasure nu] [IsFiniteMeasure mu]
    (hc0 : ∀ f : C₀(X, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, Function.extend i (fun y ↦ ENNReal.ofReal (f y)) 0 z ∂nu =
        ∫⁻ y, ENNReal.ofReal (f y) ∂mu)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, Function.extend i g 0 z ∂nu = ∫⁻ y, g y ∂mu := by
  have : IsFiniteMeasure (nu.comap i) := isFiniteMeasure_comap hi nu
  have hpull : nu.comap i = mu := by
    refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun f ↦ ?_
    set F : C₀(X, ℝ) := compactlySupportedToZeroAtInfty f.toReal with hF
    have hFapp : ∀ y, F y = (f y : ℝ) := by
      intro y
      rw [hF, compactlySupportedToZeroAtInfty_apply,
        CompactlySupportedContinuousMap.toReal_apply]
    have hF0 : ∀ y, 0 ≤ F y := fun y ↦ by rw [hFapp y]; exact (f y).coe_nonneg
    have hFmeas : Measurable fun y ↦ ENNReal.ofReal (F y) :=
      ENNReal.measurable_ofReal.comp F.continuous.measurable
    have hkey : ∫⁻ y, ENNReal.ofReal (F y) ∂nu.comap i = ∫⁻ y, ENNReal.ofReal (F y) ∂mu := by
      rw [← lintegral_extend_eq_lintegral_comap hi nu hFmeas]
      exact hc0 F hF0
    have h1 : ENNReal.ofReal (∫ y, F y ∂nu.comap i) =
        ∫⁻ y, ENNReal.ofReal (F y) ∂nu.comap i :=
      ofReal_integral_eq_lintegral_ofReal (F.toBCF.integrable (nu.comap i))
        (Eventually.of_forall hF0)
    have h2 : ENNReal.ofReal (∫ y, F y ∂mu) = ∫⁻ y, ENNReal.ofReal (F y) ∂mu :=
      ofReal_integral_eq_lintegral_ofReal (F.toBCF.integrable mu) (Eventually.of_forall hF0)
    have hreal : ENNReal.ofReal (∫ y, F y ∂nu.comap i) = ENNReal.ofReal (∫ y, F y ∂mu) := by
      rw [h1, hkey, ← h2]
    have hbochner : ∫ y, F y ∂nu.comap i = ∫ y, F y ∂mu :=
      (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hF0) (integral_nonneg hF0)).mp hreal
    simpa only [hFapp] using hbochner
  rw [lintegral_extend_eq_lintegral_comap hi nu hg, hpull]
