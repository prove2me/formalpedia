-- Prove2me | solution 1 for MarkovProcess.isBrownianReal_brownianMotion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:02:54.072838+00:00
-- url     : https://prove2.me/submissions/f013c3b7-d4fb-4e9d-aa47-c9dd1c7db00b

import Definitions.Def_MarkovProcess_V3H_Examples_BrownianMotion_c88465db
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
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
import Mathlib.Probability.HasLaw
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_continuousPathTrajectory_map_eval_nnreal
import Theorems.Thm_MarkovProcess_hasIndepIncrements_brownianMotion
import Theorems.Thm_MarkovProcess_hasKolmogorovMoments_heatSemigroup

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dynkin's formula at deterministic times

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
`P`, the `C₀` semigroup `hFeller.c0Semigroup` acts by `(S t f) x = E_x f(ω_t)`
(`c0Semigroup_apply_eq_integral`, from the one-time marginal `continuousProcess_map_eval_nnreal`
at every real time).  Combining this with the fundamental identity of the generator
`S t f - f = ∫₀ᵗ S s (L f) ds` and Fubini's theorem gives **Dynkin's formula**
(`integral_eval_sub_eq_integral_integral_generator`): for `f` in the generator domain,

  `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds`.

The evaluation functional `c0EvalCLM x : C₀(α, ℝ) →L[ℝ] ℝ` is the tool that moves the Bochner
integral in `C₀` to a pointwise integral; `evalC0CLM` is the same functional under its original
name, kept for consumers.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Eval

variable {alpha : Type*} [TopologicalSpace alpha]





end Eval

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- One-time marginal at every real time: evaluating the continuous-path process at time `t`
gives the transition kernel of `P` at `t`. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal) :
    (IsConservative.continuousProcess P hP).map (fun omega ↦ omega t) = P t :=
  IsConservative.continuousPathTrajectory_map_eval_nnreal P hP hFeller _ hK t









end MarkovProcess.SubMarkovKernelSemigroup


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

/-- The heat semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_heatSemigroup :
    heatSemigroup.KolmogorovRegular isConservative_heatSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_heatSemigroup hasKolmogorovMoments_heatSemigroup







/-- Every one-time marginal of Brownian motion started at `x` is the Gaussian law with mean `x`
and variance the elapsed time. -/
theorem brownianMotion_map_eval (t : NNReal) (x : ℝ) :
    (brownianMotion x).map (fun omega ↦ omega t) = gaussianReal x t := by
  have hmeas : Measurable (fun omega : ContinuousPath ℝ ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t
  rw [brownianMotion, ← Kernel.map_apply _ hmeas,
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
      heatSemigroup isConservative_heatSemigroup isFellerKernelSemigroup_heatSemigroup
      kolmogorovRegular_heatSemigroup t, heatSemigroup_apply]





end Process

end

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The process of the heat semigroup is a Brownian motion

The continuous-path process `brownianMotion` of `MarkovProcess.Examples.HeatSemigroup` is
identified as a Brownian motion on the line: recentred at its starting point it has centred
Gaussian marginals of variance the elapsed time, independent increments over the consecutive
intervals of every finite monotone family of times, and continuous trajectories.

The engine is the simple Markov property in joint-law form
(`brownianMotion_map_prodMk_shift`): the law of the pair consisting of the position at a time and
the path shifted by that time is the composition-product of the position law with the process.
Iterating it identifies the law of the vector of increments of a monotone family of times as a
product of centred Gaussians, and independence follows from the product form.

Main results:

* `brownianMotion_map_prodMk_shift`: the simple Markov property in joint-law form.
* `brownianMotion_map_incrementsMap`, `brownianMotion_map_increments`: the joint law of the
  increments is a product of centred Gaussians.
* `HasIndepIncrements`, `hasIndepIncrements_brownianMotion`: independence of the increments.
* `IsBrownianReal`, `isBrownianReal_brownianMotion`: the identification.

`HasIndepIncrements` copies the definition of Mathlib's
`Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.lean`; `IsBrownianReal` is
the form that Mathlib's `Mathlib/Probability/BrownianMotion/Basic.lean` proves equivalent to its
own definition of `IsBrownianReal` (`HasIndepIncrements.isPreBrownianReal_of_hasLaw` and the
converse lemmas `IsPreBrownianReal.hasLaw_eval`, `IsPreBrownianReal.hasIndepIncrements`).
Neither is available at the pinned revision, and `IsBrownianReal` here is stated through Gaussian
marginals and independent increments, not through a projective family.  Only one space dimension is treated, and no
Levy characterization, quadratic variation, or stochastic integral is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

section MarkovProperty





end MarkovProperty

section Increments

























end Increments

section IndependentIncrements













end IndependentIncrements

section Identification





end Identification

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The process of the heat semigroup is a Brownian motion

The continuous-path process `brownianMotion` of `MarkovProcess.Examples.HeatSemigroup` is
identified as a Brownian motion on the line: recentred at its starting point it has centred
Gaussian marginals of variance the elapsed time, independent increments over the consecutive
intervals of every finite monotone family of times, and continuous trajectories.

The engine is the simple Markov property in joint-law form
(`brownianMotion_map_prodMk_shift`): the law of the pair consisting of the position at a time and
the path shifted by that time is the composition-product of the position law with the process.
Iterating it identifies the law of the vector of increments of a monotone family of times as a
product of centred Gaussians, and independence follows from the product form.

Main results:

* `brownianMotion_map_prodMk_shift`: the simple Markov property in joint-law form.
* `brownianMotion_map_incrementsMap`, `brownianMotion_map_increments`: the joint law of the
  increments is a product of centred Gaussians.
* `HasIndepIncrements`, `hasIndepIncrements_brownianMotion`: independence of the increments.
* `IsBrownianReal`, `isBrownianReal_brownianMotion`: the identification.

`HasIndepIncrements` copies the definition of Mathlib's
`Mathlib/Probability/Independence/Process/HasIndepIncrements/Basic.lean`; `IsBrownianReal` is
the form that Mathlib's `Mathlib/Probability/BrownianMotion/Basic.lean` proves equivalent to its
own definition of `IsBrownianReal` (`HasIndepIncrements.isPreBrownianReal_of_hasLaw` and the
converse lemmas `IsPreBrownianReal.hasLaw_eval`, `IsPreBrownianReal.hasIndepIncrements`).
Neither is available at the pinned revision, and `IsBrownianReal` here is stated through Gaussian
marginals and independent increments, not through a projective family.  Only one space dimension is treated, and no
Levy characterization, quadratic variation, or stochastic integral is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal









namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (x : ℝ) :
    IsBrownianReal (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (brownianMotion x) where
  hasLaw_eval t := by
    refine ⟨((ContinuousPath.measurable_coordinateProcess t).sub measurable_const).aemeasurable, ?_⟩
    have hmeas : Measurable (fun omega : ContinuousPath ℝ ↦ omega t) :=
      ContinuousPath.measurable_coordinateProcess t
    have hsub : Measurable (fun u : ℝ ↦ u - x) := by fun_prop
    rw [show (fun omega : ContinuousPath ℝ ↦ omega t - x)
        = (fun u : ℝ ↦ u - x) ∘ (fun omega : ContinuousPath ℝ ↦ omega t) from rfl,
      ← Measure.map_map hsub hmeas, brownianMotion_map_eval, gaussianReal_map_sub_const x,
      sub_self]
  hasIndepIncrements := hasIndepIncrements_brownianMotion x
  cont := Filter.Eventually.of_forall fun omega ↦ omega.continuous.sub continuous_const
