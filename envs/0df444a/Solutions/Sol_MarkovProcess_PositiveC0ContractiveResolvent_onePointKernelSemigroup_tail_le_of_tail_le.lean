-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.onePointKernelSemigroup_tail_le_of_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:50:39.243852+00:00
-- url     : https://prove2.me/submissions/3da9bc35-37b3-4473-994a-1f20ba98c8e3

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
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_onePointKernelSemigroup_apply_coe

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kolmogorov bounds on a one-point compactification

This file provides a compatible metric on the one-point compactification and a local-time form of
the intrinsic Kolmogorov moment criterion. It transports whole-space distance tails, including
the cemetery point, to that local criterion by the weighted layer-cake formula.

Main results: `OnePoint.exhaustionMetricSpace`,
`SubMarkovKernelSemigroup.HasLocalKolmogorovMoments.toHasKolmogorovMoments`, and
`SubMarkovKernelSemigroup.HasOnePointTailBounds.kolmogorovRegular`.

The tail bounds and their scalar integral budget remain hypotheses for the consumer; no analytic
estimate for a particular semigroup is asserted here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace OnePoint

variable {X : Type*} [MetricSpace X]

































/-- A live exhaustion-metric tail is contained in the corresponding tail for the original
metric. -/
theorem exhaustionMetricSpace_live_tail_subset (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) (x : X) (r : ℝ) :
    letI := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    {y : X | r < dist (y : OnePoint X) (x : OnePoint X)} ⊆ {y | r < dist y x} := by
  let := exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  intro y hy
  exact hy.trans_le (exhaustionMetricSpace_dist_coe_coe_le rho hrho_cont hrho_pos
    hrho_lipschitz hrho_compact y x)

end OnePoint

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]



namespace HasLocalKolmogorovMoments

variable {P : SubMarkovKernelSemigroup alpha} {p q : ℝ} {M B : ℝ≥0}



end HasLocalKolmogorovMoments

section OnePointTails

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] (rho : X → ℝ) (hrho_cont : Continuous rho)
  (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
  (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})











namespace HasOnePointTailBounds

variable {rho : X → ℝ} {hrho_cont : Continuous rho} {hrho_pos : ∀ x, 0 < rho x}
  {hrho_lipschitz : LipschitzWith 1 rho}
  {hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}}
variable {P : SubMarkovKernelSemigroup (OnePoint X)} {p q : ℝ} {M B : ℝ≥0}
  {phi : ℝ≥0 → X → ℝ → ℝ≥0∞}







end HasOnePointTailBounds

end OnePointTails

end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]



end MarkovProcess.PositiveC0ContractiveResolvent


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
    (h : NNReal) (x : X) (r : ℝ) (a : ℝ≥0∞)
    (hlive : R.kernelSemigroup h x {y | r < dist y x} ≤ a)
    (hcemetery : R.onePointKernelSemigroup h (x : OnePoint X) {OnePoint.infty} =
      1 - R.kernelSemigroup h x Set.univ) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    R.onePointKernelSemigroup h (x : OnePoint X)
        {z | r < dist z (x : OnePoint X)} ≤
      a + (1 - R.kernelSemigroup h x Set.univ) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let tail : Set (OnePoint X) := {z | r < dist z (x : OnePoint X)}
  let live : Set (OnePoint X) := Set.range ((↑) : X → OnePoint X)
  have htail : MeasurableSet tail :=
    measurableSet_lt measurable_const
      (measurable_dist.comp (measurable_id.prodMk measurable_const))
  have hliveSet : MeasurableSet live := OnePoint.isOpen_range_coe.measurableSet
  have hliveBound :
      R.onePointKernelSemigroup h (x : OnePoint X) (tail ∩ live) ≤ a := by
    rw [R.onePointKernelSemigroup_apply_coe h x, Measure.add_apply,
      Measure.map_apply OnePoint.continuous_coe.measurable (htail.inter hliveSet),
      Measure.smul_apply, Measure.dirac_apply' OnePoint.infty (htail.inter hliveSet)]
    have hinfty : OnePoint.infty ∉ tail ∩ live :=
      fun hz ↦ OnePoint.infty_notMem_range_coe hz.2
    rw [Set.indicator_of_notMem hinfty, smul_zero, add_zero]
    apply (measure_mono ?_).trans hlive
    intro y hy
    exact OnePoint.exhaustionMetricSpace_live_tail_subset rho hrho_cont hrho_pos
      hrho_lipschitz hrho_compact x r hy.1
  have hcover : tail ⊆ (tail ∩ live) ∪ {OnePoint.infty} := by
    intro z hz
    induction z using OnePoint.rec with
    | infty => exact Set.mem_union_right _ (Set.mem_singleton _)
    | coe y => exact Set.mem_union_left _ ⟨hz, ⟨y, rfl⟩⟩
  calc
    R.onePointKernelSemigroup h (x : OnePoint X) tail ≤
        R.onePointKernelSemigroup h (x : OnePoint X)
          ((tail ∩ live) ∪ {OnePoint.infty}) := measure_mono hcover
    _ ≤ R.onePointKernelSemigroup h (x : OnePoint X) (tail ∩ live) +
        R.onePointKernelSemigroup h (x : OnePoint X) {OnePoint.infty} := measure_union_le _ _
    _ ≤ a + (1 - R.kernelSemigroup h x Set.univ) :=
      add_le_add hliveBound hcemetery.le
