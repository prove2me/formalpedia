-- Prove2me | solution 1 for MarkovProcess.generator_heatSemigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:43:31.152889+00:00
-- url     : https://prove2.me/submissions/8a8fc0da-6f72-40f5-bfa2-17608f8337d2

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
# The generator of a strongly continuous contraction semigroup

For `S : StronglyContinuousContractionSemigroup E` this file defines the generator domain
`S.generatorDomain`, the submodule of vectors `f` whose difference quotients
`t⁻¹ • (S t f - f)` converge as `t → 0⁺`, and the generator
`S.generator : S.generatorDomain →ₗ[ℝ] E` as that limit.  The main results are:

* `tendsto_generator`: the defining limit, and `generator_eq_of_tendsto`, its uniqueness;
* `operator_mem_generatorDomain` and `generator_operator`: the domain is invariant under every
  `S t`, and `S t` commutes with the generator;
* `tendsto_differenceQuotient_add`: every orbit `t ↦ S t f` of a vector in the domain is right
  differentiable at every time, with derivative `S t (S.generator f)`; its real-variable forms are
  `hasDerivWithinAt_Ioi` and `hasDerivWithinAt_Ici`, and at positive times the derivative is
  two-sided, `hasDerivAt_operator_toNNReal`;
* `operator_sub_eq_integral` and `exp_smul_operator_sub_eq_integral`: the fundamental identity
  and its exponentially weighted form;
* `orbitIntegral_mem_generatorDomain` and `generator_orbitIntegral`: for every vector `f`, the
  orbit integral `∫₀ᵗ S s f ds` lies in the domain with generator `S t f - f`; hence
  `dense_generatorDomain`, the domain is dense.

Times are `NNReal` throughout the library; the real-variable statements read the semigroup at
`Real.toNNReal s`.  The fundamental identity is what Dynkin's formula consumes.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

section DifferenceQuotient













end DifferenceQuotient

section Domain







end Domain

section Generator















/-- The generator of a vector given by a convergence proof. -/
theorem generator_mk_eq {f g : E}
    (h : Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    S.generator ⟨f, S.mem_generatorDomain_of_tendsto h⟩ = g :=
  S.generator_eq_of_tendsto _ h

end Generator

section Invariance







end Invariance

section RealVariable















variable [CompleteSpace E]





end RealVariable

section OrbitIntegral









variable [CompleteSpace E]















end OrbitIntegral

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup


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




















namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (f g : C₀(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hg : ∀ x, g x = iteratedDeriv 2 (f : ℝ → ℝ) x) :
    isFellerKernelSemigroup_heatSemigroup.c0Semigroup.generator
      ⟨f, mem_generatorDomain_heatSemigroup f g hf hg⟩ = (2 : ℝ)⁻¹ • g :=
  isFellerKernelSemigroup_heatSemigroup.c0Semigroup.generator_mk_eq
    (tendsto_differenceQuotient_heatSemigroup f g hf hg)
