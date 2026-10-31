-- Prove2me | solution 1 for MarkovProcess.abs_sub_taylor_two_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:48:00.498618+00:00
-- url     : https://prove2.me/submissions/9997ee68-28e7-44c9-9464-82b3ee2695a3

import Definitions.Def_MarkovProcess_V3H_Examples_HeatGenerator_9a0037cf
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
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
# Gaussian averages and half the Laplacian on the line

Half the second derivative — half the Laplacian in one dimension — is the infinitesimal
generator of the Gaussian averages of a twice continuously differentiable function whose value
and second derivative vanish at infinity.  Writing `gaussianReal x t` for the normal law on the
line with mean `x` and variance `t`, and `x ↦ ∫ f d gaussianReal x t` for the Gaussian average
of `f` at scale `t` (at `t = 0` it is `f` itself), the difference quotient
`t⁻¹ (∫ f d gaussianReal x t - f x)` converges to `f'' x / 2` as `t → 0⁺`, uniformly in the
centre `x`.  The argument is the classical one: rescaling by `√t` reduces every average to the
standard normal law, and a second-order Taylor expansion at `x` splits the increment into a term
of first order whose Gaussian mean vanishes, a term of second order whose Gaussian mean is
`t f'' x / 2`, and a remainder bounded by the modulus of continuity of `f''` on the bulk of the
law and by its fourth moment on the tail.  Neither bound depends on `x`, whence the uniformity.

Main results:

* `abs_sub_taylor_two_le`, the second-order Taylor estimate with a modulus: the second-order
  Taylor polynomial of `f` at `x` approximates `f (x + h)` to within `C h²` as soon as the
  increment of `f''` over the segment from `x` to `x + h` is at most `C`;
* `tendstoUniformly_gaussianAverage_sub_div`, the limit above, as a `TendstoUniformly`
  statement;
* `gaussianAverage`, the Gaussian average of a continuous function vanishing at infinity: the
  `C₀` action of the heat semigroup of `Examples/HeatSemigroup.lean`, and
  `tendsto_gaussianAverage_sub_div`, the same limit read as convergence in the `C₀` norm;
* `c0Semigroup_heatSemigroup_apply`, `tendsto_differenceQuotient_heatSemigroup`,
  `mem_generatorDomain_heatSemigroup` and `generator_heatSemigroup`: twice continuously
  differentiable `C₀` functions with `C₀` second derivative lie in the generator domain of the
  `C₀` semigroup of the heat semigroup, and the generator is half the second derivative there,
  in the sense of `Semigroup/Generator.lean`.

No partial differential equation is solved, the generator domain is not characterized (only
contained), and nothing is claimed in dimension greater than one or for a function outside the
stated smoothness class.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

section Taylor

variable {f : ℝ → ℝ}



end Taylor

section Gaussian













end Gaussian

section Estimate

variable {f : ℝ → ℝ}





end Estimate

section Uniform

variable {f : ℝ → ℝ}





end Uniform

section C0















end C0

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Gaussian averages and half the Laplacian on the line

Half the second derivative — half the Laplacian in one dimension — is the infinitesimal
generator of the Gaussian averages of a twice continuously differentiable function whose value
and second derivative vanish at infinity.  Writing `gaussianReal x t` for the normal law on the
line with mean `x` and variance `t`, and `x ↦ ∫ f d gaussianReal x t` for the Gaussian average
of `f` at scale `t` (at `t = 0` it is `f` itself), the difference quotient
`t⁻¹ (∫ f d gaussianReal x t - f x)` converges to `f'' x / 2` as `t → 0⁺`, uniformly in the
centre `x`.  The argument is the classical one: rescaling by `√t` reduces every average to the
standard normal law, and a second-order Taylor expansion at `x` splits the increment into a term
of first order whose Gaussian mean vanishes, a term of second order whose Gaussian mean is
`t f'' x / 2`, and a remainder bounded by the modulus of continuity of `f''` on the bulk of the
law and by its fourth moment on the tail.  Neither bound depends on `x`, whence the uniformity.

Main results:

* `abs_sub_taylor_two_le`, the second-order Taylor estimate with a modulus: the second-order
  Taylor polynomial of `f` at `x` approximates `f (x + h)` to within `C h²` as soon as the
  increment of `f''` over the segment from `x` to `x + h` is at most `C`;
* `tendstoUniformly_gaussianAverage_sub_div`, the limit above, as a `TendstoUniformly`
  statement;
* `gaussianAverage`, the Gaussian average of a continuous function vanishing at infinity: the
  `C₀` action of the heat semigroup of `Examples/HeatSemigroup.lean`, and
  `tendsto_gaussianAverage_sub_div`, the same limit read as convergence in the `C₀` norm;
* `c0Semigroup_heatSemigroup_apply`, `tendsto_differenceQuotient_heatSemigroup`,
  `mem_generatorDomain_heatSemigroup` and `generator_heatSemigroup`: twice continuously
  differentiable `C₀` functions with `C₀` second derivative lie in the generator domain of the
  `C₀` semigroup of the heat semigroup, and the generator is half the second derivative there,
  in the sense of `Semigroup/Generator.lean`.

No partial differential equation is solved, the generator domain is not characterized (only
contained), and nothing is claimed in dimension greater than one or for a function outside the
stated smoothness class.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty




variable {f : ℝ → ℝ}

namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (hf : ContDiff ℝ 2 f) (x h C : ℝ)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 2 f (x + s * h) - iteratedDeriv 2 f x| ≤ C) :
    |f (x + h) - f x - h * deriv f x - h ^ 2 / 2 * iteratedDeriv 2 f x| ≤ C * h ^ 2 := by
  have hd2 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hddf : Differentiable ℝ (deriv f) := hd2.differentiable (by norm_num)
  have hiter : ∀ y : ℝ, deriv (deriv f) y = iteratedDeriv 2 f y := by
    intro y; rw [iteratedDeriv_succ, iteratedDeriv_one]
  set c := iteratedDeriv 2 f x with hcdef
  have hinner : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ x + s * h) h s := by
    intro s
    simpa using (((hasDerivAt_id s).mul_const h).const_add x)
  set F : ℝ → ℝ :=
    fun s ↦ f (x + s * h) - f x - s * (h * deriv f x) - s ^ 2 * (h ^ 2 * c / 2) with hFdef
  set G : ℝ → ℝ := fun s ↦ h * deriv f (x + s * h) - h * deriv f x - s * (h ^ 2 * c) with hGdef
  have hFderiv : ∀ s : ℝ, HasDerivAt F (G s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ ↦ f (x + s * h)) (deriv f (x + s * h) * h) s :=
      (hdf (x + s * h)).hasDerivAt.comp s (hinner s)
    have h2 : HasDerivAt (fun s : ℝ ↦ s * (h * deriv f x)) (h * deriv f x) s := by
      simpa using (hasDerivAt_id s).mul_const (h * deriv f x)
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 2 * (h ^ 2 * c / 2)) (2 * s * (h ^ 2 * c / 2)) s := by
      have hp : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
      exact hp.mul_const _
    have hsum := ((h1.sub_const (f x)).sub h2).sub h3
    convert hsum using 1
    all_goals first | rfl | ring
  have hGderiv : ∀ s : ℝ, HasDerivAt G (h ^ 2 * (iteratedDeriv 2 f (x + s * h) - c)) s := by
    intro s
    have h1 := (hddf (x + s * h)).hasDerivAt.comp s (hinner s)
    simp only [Function.comp_def, hiter] at h1
    have h2 : HasDerivAt (fun s : ℝ ↦ s * (h ^ 2 * c)) (h ^ 2 * c) s := by
      simpa using (hasDerivAt_id s).mul_const (h ^ 2 * c)
    have hsum := ((h1.const_mul h).sub_const (h * deriv f x)).sub h2
    convert hsum using 1
    all_goals first | rfl | ring
  have hCnn : 0 ≤ C := by
    have h0 := hC 0 (by norm_num)
    rw [zero_mul, add_zero, ← hcdef, sub_self, abs_zero] at h0
    exact h0
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hGbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖G s‖ ≤ C * h ^ 2 := by
    intro s hs
    have hkey : ‖G s - G 0‖ ≤ C * h ^ 2 * ‖s - 0‖ := by
      refine hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ ↦ (hGderiv u).hasDerivWithinAt) (fun u hu ↦ ?_) (by norm_num) hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg h)]
      calc h ^ 2 * |iteratedDeriv 2 f (x + u * h) - c| ≤ h ^ 2 * C :=
            mul_le_mul_of_nonneg_left (hC u hu) (sq_nonneg h)
        _ = C * h ^ 2 := by ring
    rw [hG0, sub_zero] at hkey
    refine hkey.trans ?_
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1]
    nlinarith [mul_nonneg hCnn (sq_nonneg h), hs.1, hs.2]
  have hFbound : ‖F 1 - F 0‖ ≤ C * h ^ 2 * ‖(1 : ℝ) - 0‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ ↦ (hFderiv u).hasDerivWithinAt) hGbound (by norm_num) (by norm_num)
  rw [hF0, sub_zero, Real.norm_eq_abs] at hFbound
  simp only [hFdef, one_mul, one_pow] at hFbound
  calc |f (x + h) - f x - h * deriv f x - h ^ 2 / 2 * c|
      = |f (x + h) - f x - 1 * (h * deriv f x) - 1 * (h ^ 2 * c / 2)| := by ring_nf
    _ ≤ C * h ^ 2 * ‖(1 : ℝ) - 0‖ := by simpa using hFbound
    _ = C * h ^ 2 := by norm_num
