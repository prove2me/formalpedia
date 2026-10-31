-- Prove2me | solution 1 for MarkovProcess.timeIncrements_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:31:36.265823+00:00
-- url     : https://prove2.me/submissions/d99013cc-7e15-40ae-9c0b-5c78cb6184a8

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

section MarkovProperty





end MarkovProperty

section Increments















/-- The recursion defining the time increments. -/
theorem timeIncrements_succ {n : ℕ} (s : Fin (n + 1) → NNReal) :
    timeIncrements s = Fin.cons (s 0) (timeIncrements (fun i ↦ s i.succ - s 0)) := rfl

/-- The first time increment is the first time itself. -/
@[simp]
theorem timeIncrements_zero_apply {n : ℕ} (s : Fin (n + 1) → NNReal) :
    timeIncrements s 0 = s 0 := rfl







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
theorem solution : ∀ {n : ℕ} {s : Fin (n + 1) → NNReal}, Monotone s →
    ∀ i : Fin n, timeIncrements s i.succ = s i.succ - s i.castSucc := by
  intro n
  induction n with
  | zero => exact fun _ i ↦ i.elim0
  | succ n ih =>
    intro s hs i
    have hs' : Monotone (fun i : Fin (n + 1) ↦ s i.succ - s 0) := fun a b hab ↦
      tsub_le_tsub_right (hs (Fin.succ_le_succ_iff.mpr hab)) _
    rw [timeIncrements_succ, Fin.cons_succ]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [timeIncrements_zero_apply]
      rfl
    · rw [ih hs' j]
      rw [← Fin.succ_castSucc,
        tsub_tsub_tsub_cancel_right (hs (Fin.zero_le _))]
