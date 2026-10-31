-- Prove2me | solution 1 for MarkovProcess.exists_norm_c0Operator_sub_le_heatSemigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:44:01.330118+00:00
-- url     : https://prove2.me/submissions/fc0c54ac-1ec2-43af-b232-82b971bf1ada

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
import Theorems.Thm_MarkovProcess_exists_measure_abs_ge_lt

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





private theorem integrable_c0_comp (f : C₀(ℝ, ℝ)) (t : NNReal) (x : ℝ) :
    Integrable (fun z ↦ f (x + Real.sqrt t * z)) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const ‖f‖) ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact norm_apply_le_norm_c0 f _















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
theorem solution (f : C₀(ℝ, ℝ)) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h : NNReal, (h : ℝ) < delta →
      ‖heatSemigroup.c0Operator mapsC0_heatSemigroup h f - f‖ ≤ eps := by
  obtain ⟨delta0, hdelta0, huc⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  have hfpos : (0 : ℝ) < 4 * (‖f‖ + 1) := by positivity
  obtain ⟨R, hR, hRmeas⟩ := exists_measure_abs_ge_lt (gaussianReal 0 1)
    (eps := eps / (4 * (‖f‖ + 1))) (by positivity)
  set S : Set ℝ := {z : ℝ | R ≤ |z|} with hS
  have hSmeas : MeasurableSet S := (isClosed_le continuous_const continuous_abs).measurableSet
  set bound : ℝ → ℝ := fun z ↦ eps / 2 + 2 * ‖f‖ * S.indicator (fun _ ↦ (1 : ℝ)) z with hbound
  have hindInt : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (gaussianReal 0 1) :=
    (integrable_indicator_iff hSmeas).mpr (integrableOn_const (measure_ne_top _ _))
  have hboundInt : Integrable bound (gaussianReal 0 1) :=
    (integrable_const (μ := gaussianReal 0 1) (eps / 2)).add (hindInt.const_mul _)
  have hboundIntegral : ∫ z, bound z ∂(gaussianReal 0 1) ≤ eps := by
    rw [hbound, integral_add (integrable_const (μ := gaussianReal 0 1) (eps / 2))
      (hindInt.const_mul _), integral_const, MeasureTheory.integral_const_mul,
      integral_indicator_const (1 : ℝ) hSmeas]
    have hnorm : 0 ≤ ‖f‖ := norm_nonneg f
    have hkey : 2 * ‖f‖ * ((gaussianReal 0 1).real S) ≤ eps / 2 := by
      have hpos : (0 : ℝ) ≤ (gaussianReal 0 1).real S := measureReal_nonneg
      calc 2 * ‖f‖ * ((gaussianReal 0 1).real S)
          ≤ 2 * (‖f‖ + 1) * (eps / (4 * (‖f‖ + 1))) := by
            apply mul_le_mul _ (le_of_lt hRmeas) hpos (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith only []) (by norm_num)
        _ = eps / 2 := by field_simp; ring
    rw [probReal_univ]
    simp only [smul_eq_mul, mul_one]
    linarith only [hkey]
  refine ⟨(delta0 / R) ^ 2, by positivity, fun h hh ↦ ?_⟩
  have hsqrt : Real.sqrt h * R < delta0 := by
    have h1 : Real.sqrt h < delta0 / R := by
      have := Real.sqrt_lt_sqrt h.coe_nonneg hh
      rwa [Real.sqrt_sq (by positivity)] at this
    calc Real.sqrt h * R < (delta0 / R) * R := by
          exact mul_lt_mul_of_pos_right h1 hR
      _ = delta0 := div_mul_cancel₀ delta0 (ne_of_gt hR)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (le_of_lt heps)).2 fun x ↦ ?_
  show ‖heatSemigroup.c0Operator mapsC0_heatSemigroup h f x - f x‖ ≤ eps
  rw [SubMarkovKernelSemigroup.c0Operator_apply, kernelIntegral_heatSemigroup]
  have hsub : (∫ z, f (x + Real.sqrt h * z) ∂(gaussianReal 0 1)) - f x =
      ∫ z, (f (x + Real.sqrt h * z) - f x) ∂(gaussianReal 0 1) := by
    rw [integral_sub (integrable_c0_comp f h x) (integrable_const (f x)), integral_const,
      probReal_univ, one_smul]
  rw [hsub]
  refine le_trans (norm_integral_le_of_norm_le hboundInt
    (Filter.Eventually.of_forall fun z ↦ ?_)) hboundIntegral
  by_cases hz : z ∈ S
  · have h1 : ‖f (x + Real.sqrt h * z) - f x‖ ≤ 2 * ‖f‖ := by
      calc ‖f (x + Real.sqrt h * z) - f x‖ ≤ ‖f (x + Real.sqrt h * z)‖ + ‖f x‖ :=
            norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (norm_apply_le_norm_c0 f _) (norm_apply_le_norm_c0 f _)
        _ = 2 * ‖f‖ := by ring
    rw [hbound]
    simp only [Set.indicator_of_mem hz, mul_one]
    linarith only [h1, heps]
  · have hdist : dist (x + Real.sqrt h * z) x < delta0 := by
      rw [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hzR : |z| < R := lt_of_not_ge (by simpa only [hS, Set.mem_ofPred_eq] using hz)
      calc Real.sqrt h * |z| ≤ Real.sqrt h * R :=
            mul_le_mul_of_nonneg_left (le_of_lt hzR) (Real.sqrt_nonneg _)
        _ < delta0 := hsqrt
    have h2 : ‖f (x + Real.sqrt h * z) - f x‖ ≤ eps / 2 := by
      rw [← dist_eq_norm]
      exact le_of_lt (huc hdist)
    rw [hbound]
    simp only [Set.indicator_of_notMem hz, mul_zero, add_zero]
    exact h2
