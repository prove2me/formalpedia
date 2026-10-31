-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.measure_gt_le_of_le_c0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:44:51.77395+00:00
-- url     : https://prove2.me/submissions/069db6a8-c4c6-4568-924b-0558a8acb0dc

import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointExtension_e4fabfdf
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
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
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
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


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
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

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha]





variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] (rho : X → ℝ) (hrho_cont : Continuous rho)
  (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
  (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})







namespace MarkovProcess.SubMarkovKernelSemigroup
end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
omit [LocallyCompactSpace X] [SecondCountableTopology X] in

theorem solution (P : SubMarkovKernelSemigroup (OnePoint X))
    (rho : X → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (h : ℝ≥0) (x : X) (r A theta : ℝ) (v : C₀(OnePoint X, ℝ))
    (hA : 0 < A) (hv_nonneg : ∀ z, 0 ≤ v z)
    (hmajorant : ∀ z, r < OnePoint.exhaustionDist rho z (x : OnePoint X) → A ≤ v z)
    (hintegral : ∫ z, v z ∂P h (x : OnePoint X) ≤
      Real.exp (theta * (h : ℝ)) * v (x : OnePoint X)) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    P h (x : OnePoint X) {z | r < dist z (x : OnePoint X)} ≤
      ENNReal.ofReal (Real.exp (theta * (h : ℝ)) * v (x : OnePoint X) / A) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let mu := P h (x : OnePoint X)
  let : IsFiniteMeasure mu :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one h (x : OnePoint X)) ENNReal.one_lt_top⟩
  have hv_integrable : Integrable v mu := v.toBCF.integrable mu
  have hmajorant' :
      {z : OnePoint X | r < dist z (x : OnePoint X)} ⊆
        {z | ENNReal.ofReal A ≤ ENNReal.ofReal (v z)} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal (hmajorant z hz)
  calc
    mu {z | r < dist z (x : OnePoint X)} ≤
        mu {z | ENNReal.ofReal A ≤ ENNReal.ofReal (v z)} := measure_mono hmajorant'
    _ ≤ (∫⁻ z, ENNReal.ofReal (v z) ∂mu) / ENNReal.ofReal A := by
      apply meas_ge_le_lintegral_div
      · exact (ENNReal.measurable_ofReal.comp v.continuous.measurable).aemeasurable
      · exact (ENNReal.ofReal_pos.mpr hA).ne'
      · exact ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (∫ z, v z ∂mu) / ENNReal.ofReal A := by
      rw [ofReal_integral_eq_lintegral_ofReal hv_integrable
        (Eventually.of_forall hv_nonneg)]
    _ ≤ ENNReal.ofReal (Real.exp (theta * (h : ℝ)) * v (x : OnePoint X)) /
        ENNReal.ofReal A := by
      gcongr
    _ = ENNReal.ofReal (Real.exp (theta * (h : ℝ)) * v (x : OnePoint X) / A) := by
      rw [ENNReal.ofReal_div_of_pos hA]
