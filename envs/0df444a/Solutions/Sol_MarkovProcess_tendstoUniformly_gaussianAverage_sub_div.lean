-- Prove2me | solution 1 for MarkovProcess.tendstoUniformly_gaussianAverage_sub_div
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:45:07.358721+00:00
-- url     : https://prove2.me/submissions/46eca830-95ae-4170-a66e-b605011b6468

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
import Theorems.Thm_MarkovProcess_abs_sub_taylor_two_le
import Theorems.Thm_MarkovProcess_gaussianReal_eq_map_add_sqrt_mul

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

/-- All polynomial moments of the standard normal law are finite. -/
private theorem integrable_pow_gaussian (n : ℕ) :
    Integrable (fun z : ℝ ↦ z ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (by simp) n

/-- The first moment of the standard normal law vanishes. -/
private theorem integral_id_gaussian : ∫ z : ℝ, z ∂(gaussianReal 0 1) = 0 :=
  integral_id_gaussianReal

/-- The second moment of the standard normal law is one. -/
private theorem integral_sq_gaussian : ∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hvar : Var[fun z : ℝ ↦ z; gaussianReal 0 1] = ((1 : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at hvar
  simpa using hvar

/-- The fourth moment of the standard normal law. -/
private def gaussianMoment4 : ℝ := ∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 1)

private theorem gaussianMoment4_nonneg : 0 ≤ gaussianMoment4 :=
  integral_nonneg fun z ↦ by positivity

/-- The Gaussian average, read on the standard normal law. -/
private theorem integral_gaussian_eq (g : ℝ → ℝ) (hg : Continuous g) (x : ℝ) (t : ℝ≥0) :
    ∫ y, g y ∂gaussianReal x t = ∫ z, g (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
  rw [gaussianReal_eq_map_add_sqrt_mul x t, integral_map (by fun_prop) hg.aestronglyMeasurable]

end Gaussian

section Estimate

variable {f : ℝ → ℝ}

/-- A pure-algebra step: away from the origin a constant is dominated by a quadratic. -/
private theorem le_mul_sq_div {M a b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (hab : b ≤ |a|) :
    M ≤ M * a ^ 2 / b ^ 2 := by
  have hsq : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs a, abs_nonneg a]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **The quantitative estimate.**  If the second derivative of `f` is bounded by `M` and varies
by at most `ε` over distances smaller than `δ`, then the Gaussian difference quotient at scale
`t` differs from half the second derivative by at most `ε` plus a term of order `t`, uniformly
in the centre `x`. -/
private theorem abs_gaussianQuotient_sub_le (hf : ContDiff ℝ 2 f) {B M ε δ : ℝ}
    (hB : ∀ y, |f y| ≤ B) (hM : ∀ y, |iteratedDeriv 2 f y| ≤ M) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hunif : ∀ u v : ℝ, |u - v| < δ → |iteratedDeriv 2 f u - iteratedDeriv 2 f v| ≤ ε)
    {t : ℝ≥0} (ht : 0 < (t : ℝ)) (x : ℝ) :
    |(t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x) - iteratedDeriv 2 f x / 2| ≤
      ε + 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM x)
  set σ := Real.sqrt (t : ℝ) with hσdef
  have hσ2 : σ ^ 2 = (t : ℝ) := Real.sq_sqrt t.coe_nonneg
  set c := iteratedDeriv 2 f x with hcdef
  have hcont : Continuous f := hf.continuous
  have hz1 : Integrable (fun z : ℝ ↦ z) (gaussianReal 0 1) := by
    simpa using integrable_pow_gaussian 1
  have hz2 : Integrable (fun z : ℝ ↦ z ^ 2) (gaussianReal 0 1) := integrable_pow_gaussian 2
  have hz4 : Integrable (fun z : ℝ ↦ z ^ 4) (gaussianReal 0 1) := integrable_pow_gaussian 4
  have hshift : Integrable (fun z : ℝ ↦ f (x + σ * z)) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const B)
      ((hcont.comp (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards with z
    simpa using hB (x + σ * z)
  have hchange : ∫ y, f y ∂gaussianReal x t = ∫ z, f (x + σ * z) ∂(gaussianReal 0 1) :=
    integral_gaussian_eq f hcont x t
  set E : ℝ → ℝ :=
    fun z ↦ f (x + σ * z) - f x - σ * z * deriv f x - (σ * z) ^ 2 / 2 * c with hEdef
  have h1 : Integrable (fun z : ℝ ↦ σ * z * deriv f x) (gaussianReal 0 1) := by
    have h := hz1.const_mul (σ * deriv f x)
    have heq : (fun z : ℝ ↦ σ * deriv f x * z) = fun z : ℝ ↦ σ * z * deriv f x := by
      funext z; ring
    rwa [heq] at h
  have h2 : Integrable (fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c) (gaussianReal 0 1) := by
    have h := hz2.const_mul (σ ^ 2 * c / 2)
    have heq : (fun z : ℝ ↦ σ ^ 2 * c / 2 * z ^ 2) = fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c := by
      funext z; ring
    rwa [heq] at h
  have hEint : Integrable E (gaussianReal 0 1) :=
    ((hshift.sub (integrable_const (f x))).sub h1).sub h2
  have hI1 : ∫ z : ℝ, σ * z * deriv f x ∂(gaussianReal 0 1) = 0 := by
    have heq : (fun z : ℝ ↦ σ * z * deriv f x) = fun z : ℝ ↦ σ * deriv f x * z := by
      funext z; ring
    rw [heq, integral_const_mul, integral_id_gaussian, mul_zero]
  have hI2 : ∫ z : ℝ, (σ * z) ^ 2 / 2 * c ∂(gaussianReal 0 1) = (t : ℝ) * c / 2 := by
    have heq : (fun z : ℝ ↦ (σ * z) ^ 2 / 2 * c) = fun z : ℝ ↦ σ ^ 2 * c / 2 * z ^ 2 := by
      funext z; ring
    rw [heq, integral_const_mul, integral_sq_gaussian, mul_one, hσ2]
  have hE : ∫ z, E z ∂(gaussianReal 0 1)
      = (∫ z, f (x + σ * z) ∂(gaussianReal 0 1)) - f x - (t : ℝ) * c / 2 := by
    have e1 : ∫ z, E z ∂(gaussianReal 0 1)
        = (∫ z, (f (x + σ * z) - f x - σ * z * deriv f x) ∂(gaussianReal 0 1))
          - ∫ z, ((σ * z) ^ 2 / 2 * c) ∂(gaussianReal 0 1) :=
      integral_sub ((hshift.sub (integrable_const (f x))).sub h1) h2
    have e2 : ∫ z, (f (x + σ * z) - f x - σ * z * deriv f x) ∂(gaussianReal 0 1)
        = (∫ z, (f (x + σ * z) - f x) ∂(gaussianReal 0 1))
          - ∫ z, (σ * z * deriv f x) ∂(gaussianReal 0 1) :=
      integral_sub (hshift.sub (integrable_const (f x))) h1
    have e3 : ∫ z, (f (x + σ * z) - f x) ∂(gaussianReal 0 1)
        = (∫ z, f (x + σ * z) ∂(gaussianReal 0 1)) - ∫ _z : ℝ, f x ∂(gaussianReal 0 1) :=
      integral_sub hshift (integrable_const (f x))
    have e4 : ∫ _z : ℝ, f x ∂(gaussianReal 0 1) = f x := by simp
    rw [e1, e2, e3, e4, hI1, hI2]
    ring
  have hEbound : ∀ z : ℝ,
      |E z| ≤ ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4 := by
    intro z
    have hCbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x| ≤
          ε + 2 * M * (σ * z) ^ 2 / δ ^ 2 := by
      intro s hs
      rcases lt_or_ge |σ * z| δ with hlt | hge
      · have hclose : |x + s * (σ * z) - x| < δ := by
          rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
          calc s * |σ * z| ≤ 1 * |σ * z| :=
                mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
            _ = |σ * z| := one_mul _
            _ < δ := hlt
        have hpos : 0 ≤ 2 * M * (σ * z) ^ 2 / δ ^ 2 := by positivity
        linarith [hunif _ _ hclose]
      · have habs : |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x| ≤ 2 * M := by
          calc |iteratedDeriv 2 f (x + s * (σ * z)) - iteratedDeriv 2 f x|
              ≤ |iteratedDeriv 2 f (x + s * (σ * z))| + |iteratedDeriv 2 f x| := abs_sub _ _
            _ ≤ M + M := add_le_add (hM _) (hM _)
            _ = 2 * M := by ring
        have hstep : 2 * M ≤ 2 * M * (σ * z) ^ 2 / δ ^ 2 :=
          le_mul_sq_div (by linarith) hδ hge
        linarith
    have htaylor := abs_sub_taylor_two_le hf x (σ * z) _ hCbound
    refine le_trans htaylor (le_of_eq ?_)
    have hsq : (σ * z) ^ 2 = (t : ℝ) * z ^ 2 := by rw [mul_pow, hσ2]
    rw [hsq]
    field_simp
  have hboundInt : Integrable
      (fun z : ℝ ↦ ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4)
      (gaussianReal 0 1) := (hz2.const_mul _).add (hz4.const_mul _)
  have hIabs : |∫ z, E z ∂(gaussianReal 0 1)| ≤
      ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4 := by
    calc |∫ z, E z ∂(gaussianReal 0 1)| ≤ ∫ z, |E z| ∂(gaussianReal 0 1) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, (ε * (t : ℝ) * z ^ 2 + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * z ^ 4) ∂(gaussianReal 0 1) :=
          integral_mono hEint.abs hboundInt hEbound
      _ = ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4 := by
          rw [integral_add (hz2.const_mul _) (hz4.const_mul _), integral_const_mul,
            integral_const_mul, integral_sq_gaussian, mul_one, gaussianMoment4]
  have hkey : (t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x) - c / 2
      = (t : ℝ)⁻¹ * ∫ z, E z ∂(gaussianReal 0 1) := by
    rw [hchange, hE]
    field_simp
  rw [hkey, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le)]
  calc (t : ℝ)⁻¹ * |∫ z, E z ∂(gaussianReal 0 1)|
      ≤ (t : ℝ)⁻¹ * (ε * (t : ℝ) + 2 * M * (t : ℝ) ^ 2 / δ ^ 2 * gaussianMoment4) :=
        mul_le_mul_of_nonneg_left hIabs (inv_nonneg.mpr ht.le)
    _ = ε + 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 := by
        field_simp

end Estimate

section Uniform

variable {f : ℝ → ℝ}

/-- A continuous function vanishing at infinity is bounded and uniformly continuous. -/
private theorem exists_bound_modulus {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : Tendsto g (cocompact ℝ) (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ y, |g y| ≤ M) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u v : ℝ, |u - v| < δ → |g u - g v| ≤ ε := by
  set G : C₀(ℝ, ℝ) := ⟨⟨g, hg⟩, hg0⟩ with hG
  refine ⟨‖G‖, norm_nonneg _, fun y ↦ ?_, fun ε hε ↦ ?_⟩
  · exact norm_apply_le_norm_c0 G y
  · obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.mp
      (ZeroAtInftyContinuousMap.uniformContinuous G) ε hε
    refine ⟨δ, hδ, fun u v huv ↦ le_of_lt ?_⟩
    have hd := h (a := u) (b := v) (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at hd



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
theorem solution (hf : ContDiff ℝ 2 f)
    (hf0 : Tendsto f (cocompact ℝ) (𝓝 0))
    (hf2 : Tendsto (iteratedDeriv 2 f) (cocompact ℝ) (𝓝 0)) :
    TendstoUniformly (fun (t : ℝ≥0) (x : ℝ) ↦ (t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x))
      (fun x ↦ iteratedDeriv 2 f x / 2) (𝓝[>] 0) := by
  obtain ⟨B, -, hB, -⟩ := exists_bound_modulus hf.continuous hf0
  obtain ⟨M, hMnn, hM, hmod⟩ :=
    exists_bound_modulus (hf.continuous_iteratedDeriv 2 (by norm_num)) hf2
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hmod (ε / 2) (by linarith)
  have hKnn : 0 ≤ 2 * M * gaussianMoment4 :=
    mul_nonneg (by linarith) gaussianMoment4_nonneg
  have hK : 0 < 2 * M * gaussianMoment4 + 1 := by linarith
  set T : ℝ := ε * δ ^ 2 / (2 * (2 * M * gaussianMoment4 + 1)) with hT
  have hTpos : 0 < T := div_pos (mul_pos hε (pow_pos hδ 2)) (by linarith)
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, (t : ℝ) < T := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < T} :=
      isOpen_lt NNReal.continuous_coe continuous_const
    have hmem : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ) < T} := by simpa using hTpos
    exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [hev, self_mem_nhdsWithin] with t htT htpos
  intro x
  have htpos' : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr htpos
  have hmain := abs_gaussianQuotient_sub_le hf hB hM (by linarith : (0 : ℝ) ≤ ε / 2) hδ hδ'
    htpos' x
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt hmain ?_
  have hKt : (2 * M * gaussianMoment4 + 1) * (t : ℝ)
      < (2 * M * gaussianMoment4 + 1) * T := mul_lt_mul_of_pos_left htT hK
  have hTval : (2 * M * gaussianMoment4 + 1) * T = ε * δ ^ 2 / 2 := by
    rw [hT]; field_simp
  have hprod : 2 * M * gaussianMoment4 * (t : ℝ) < ε * δ ^ 2 / 2 := by
    nlinarith [hKt, hTval, htpos'.le]
  have hbound : 2 * M * (t : ℝ) * gaussianMoment4 / δ ^ 2 < ε / 2 := by
    rw [div_lt_iff₀ (pow_pos hδ 2)]
    nlinarith [hprod]
  linarith
