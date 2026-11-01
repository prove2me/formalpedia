-- Prove2me | solution 1 for MarkovProcess.ae_exitTime_eq_top_heatResolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:34:33.492478+00:00
-- url     : https://prove2.me/submissions/5efa1531-7511-406b-857b-807434a59517

import Definitions.Def_MarkovProcess_V3H_Examples_HeatOnePoint_42235b58
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
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
import Mathlib.Probability.Distributions.Gaussian.Real
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
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_OnePointRegular_ae_exitTime_eq_top

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservativity from the resolvent of the constant observable

A sub-Markov kernel semigroup loses no mass as soon as its resolvent at one positive shift has
the full mass of the exponential weight,

  `lam * R_lam 1 = 1`   (`SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one`).

The transition mass is nonincreasing in time (`SubMarkovKernelSemigroup.measure_univ_le_of_le`),
because the Chapman--Kolmogorov law integrates a mass at most one against an earlier transition
law.  The hypothesis says that the Laplace transform of the transition mass equals the Laplace
transform of the constant observable one; both integrands are integrable and ordered, so they
agree at almost every time, and monotonicity in time upgrades this to every time.

The converse is immediate from the mass of the exponential weight
(`SubMarkovKernelSemigroup.IsConservative.kernelResolvent_one`,
`SubMarkovKernelSemigroup.IsConservative.ofReal_mul_kernelResolvent_one`), so the criterion is an
equivalence and not merely a sufficient condition.

No topology on the state space is used.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha] (P : SubMarkovKernelSemigroup alpha)



/-- The Laplace transform of the constant observable one at a positive shift. -/
theorem lintegral_expWeight_one {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) = ENNReal.ofReal lam⁻¹ := by
  have hmass : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam = laplaceWeight lam univ :=
    lintegral_one
  have hweight : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) * 1 :=
    lintegral_laplaceWeight lam measurable_const
  simp only [mul_one] at hweight
  rw [← hweight, hmass, laplaceWeight_univ hlam]



/-- **The resolvent of the constant observable one under conservativity.**  A conservative
semigroup carries the full mass of the exponential weight, so its kernel resolvent of the
constant observable one is the reciprocal of the shift. -/
theorem IsConservative.kernelResolvent_one {P : SubMarkovKernelSemigroup alpha}
    (hP : P.IsConservative) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    P.kernelResolvent lam (fun _ ↦ 1) x = ENNReal.ofReal lam⁻¹ := by
  rw [← lintegral_expWeight_one hlam]
  unfold kernelResolvent
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ht ↦ ?_
  rw [lintegral_one, hP _ x, mul_one]

/-- **The conservativity criterion is an equivalence.**  For a conservative semigroup the shift
times the kernel resolvent of the constant observable one is one at every positive shift, which
is the converse of `isConservative_of_kernelResolvent_one`. -/
theorem IsConservative.ofReal_mul_kernelResolvent_one {P : SubMarkovKernelSemigroup alpha}
    (hP : P.IsConservative) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x = 1 := by
  rw [hP.kernelResolvent_one hlam x, ← ENNReal.ofReal_mul hlam.le,
    mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]

end MarkovProcess.SubMarkovKernelSemigroup


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The compactified heat process

The heat resolvent represents the heat semigroup again
(`kernelSemigroup_heatResolvent`), so its one-point extension moves a live starting point by the
Gaussian law and never reaches the added point.  In the metric determined by the exhaustion
`x ↦ 1 / (1 + |x|)` the distance of two points is at most `2` and the distance of two live points
is at most their distance on the line, so the fourth-moment estimate of the Gaussian law gives
the local Kolmogorov criterion on the compactification
(`hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent`).

This assembles the regularity data from which the continuous-path process of the compactified
heat semigroup is formed (`onePointRegular_heatResolvent`), the witness that those data are
available for a genuine example.  Because the heat semigroup is conservative, the compactified
process started at a live point almost surely never reaches the added point
(`ae_exitTime_eq_top_heatResolvent`).
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess



section Metric





end Metric

section Moments



end Moments





end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The compactified heat process

The heat resolvent represents the heat semigroup again
(`kernelSemigroup_heatResolvent`), so its one-point extension moves a live starting point by the
Gaussian law and never reaches the added point.  In the metric determined by the exhaustion
`x ↦ 1 / (1 + |x|)` the distance of two points is at most `2` and the distance of two live points
is at most their distance on the line, so the fourth-moment estimate of the Gaussian law gives
the local Kolmogorov criterion on the compactification
(`hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent`).

This assembles the regularity data from which the continuous-path process of the compactified
heat semigroup is formed (`onePointRegular_heatResolvent`), the witness that those data are
available for a genuine example.  Because the heat semigroup is conservative, the compactified
process started at a live point almost surely never reaches the added point
(`ae_exitTime_eq_top_heatResolvent`).
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty









namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (x : ℝ) :
    letI := onePointRegular_heatResolvent.metricSpace
    letI := onePointRegular_heatResolvent.completeSpace
    ∀ᵐ omega ∂SubMarkovKernelSemigroup.IsConservative.continuousProcess
        heatResolvent.onePointKernelSemigroup
        heatResolvent.isConservative_onePointKernelSemigroup (x : OnePoint ℝ),
      ContinuousPath.exitTime (Set.range ((↑) : ℝ → OnePoint ℝ)) omega = ⊤ :=
  onePointRegular_heatResolvent.ae_exitTime_eq_top one_pos x (by
    rw [kernelSemigroup_heatResolvent]
    exact isConservative_heatSemigroup.ofReal_mul_kernelResolvent_one one_pos x)
