-- Prove2me | solution 1 for MarkovProcess.exists_measure_abs_ge_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:28:36.999223+00:00
-- url     : https://prove2.me/submissions/191eb8b0-bd01-4411-8c6d-be6df7577ce1

import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Trajectory_Dynkin_eb6ae7c0
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
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
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
# The one-dimensional heat semigroup and its continuous-path process

The transition semigroup on the real line whose kernel at time `t` is the Gaussian law with mean
the starting point and variance `t`.  It is conservative, Feller, and satisfies the Kolmogorov
moment criterion with exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as
constant, so the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.  The
process it produces is named `brownianMotion`.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its Gaussian transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `heatResolvent`: its positive contractive `C₀` resolvent.
* `heatExhaustion`: the explicit exhaustion `x ↦ 1 / (1 + |x|)`.
* `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov moment bound.
* `existsUnique_continuousProcess_heatSemigroup`: the main theorem, applied.
* `brownianMotion`, `brownianMotion_map_eval`, `brownianMotion_map_finsetEvaluation`: the
  continuous-path process and its finite-dimensional distributions.

Only one space dimension is treated: the multidimensional heat semigroup is not constructed here.
Nothing in this file asserts independence of increments; that is proved in
`MarkovProcess.Examples.BrownianMotion`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

section Gaussian





end Gaussian

section Definition





















end Definition

section Feller





















end Feller

section OnePointExhaustion













end OnePointExhaustion

section Moments











end Moments

section Process















end Process

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The one-dimensional heat semigroup and its continuous-path process

The transition semigroup on the real line whose kernel at time `t` is the Gaussian law with mean
the starting point and variance `t`.  It is conservative, Feller, and satisfies the Kolmogorov
moment criterion with exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as
constant, so the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.  The
process it produces is named `brownianMotion`.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its Gaussian transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `heatResolvent`: its positive contractive `C₀` resolvent.
* `heatExhaustion`: the explicit exhaustion `x ↦ 1 / (1 + |x|)`.
* `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov moment bound.
* `existsUnique_continuousProcess_heatSemigroup`: the main theorem, applied.
* `brownianMotion`, `brownianMotion_map_eval`, `brownianMotion_map_finsetEvaluation`: the
  continuous-path process and its finite-dimensional distributions.

Only one space dimension is treated: the multidimensional heat semigroup is not constructed here.
Nothing in this file asserts independence of increments; that is proved in
`MarkovProcess.Examples.BrownianMotion`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty














namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (nu : Measure ℝ) [IsFiniteMeasure nu] {eps : ℝ}
    (heps : 0 < eps) : ∃ R : ℝ, 0 < R ∧ (nu {z : ℝ | R ≤ |z|}).toReal < eps := by
  have hmeasA : ∀ n : ℕ, NullMeasurableSet {z : ℝ | (n : ℝ) ≤ |z|} nu := fun n ↦
    ((isClosed_le continuous_const continuous_abs).measurableSet).nullMeasurableSet
  have hanti : Antitone (fun n : ℕ ↦ {z : ℝ | (n : ℝ) ≤ |z|}) := by
    intro n m hnm z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    exact le_trans (Nat.cast_le.mpr hnm) hz
  have hempty : (⋂ n : ℕ, {z : ℝ | (n : ℝ) ≤ |z|}) = (∅ : Set ℝ) := by
    refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt |z|
    exact absurd (Set.mem_iInter.mp hz n) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hmeasA hanti ⟨0, measure_ne_top nu _⟩
  rw [hempty, measure_empty] at htend
  have hev : ∀ᶠ n : ℕ in atTop, nu {z : ℝ | (n : ℝ) ≤ |z|} < ENNReal.ofReal eps :=
    htend.eventually_lt_const (by simpa using heps)
  obtain ⟨n, hn⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨(n : ℝ), by exact_mod_cast hn.2, ENNReal.toReal_lt_of_lt_ofReal hn.1⟩
