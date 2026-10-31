-- Prove2me | solution 1 for MarkovProcess.localResolvent_le_minimalResolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:29:54.745811+00:00
-- url     : https://prove2.me/submissions/be06d4f7-6908-4415-843b-b95c9077a4ec

import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingMinimal_1c9dd1e4
import Definitions.Def_MarkovProcess_V3H_Killed_GluingResolventEquation_b19dddc8
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The supremum resolvent (the minimal process of Blumenthal--Getoor, in name only)

A family of positive `C₀`-contractive resolvents `R m` on local state spaces `X m`, embedded as
an increasing family of open subsets of an ambient measurable space, is glued here at the level
of resolvents.  Each `R m` is transported to the ambient space by extending its kernel resolvent
by zero off the `m`-th domain (`localResolvent`).  Under the part-process identity of
`Killed/GluingLocal.lean` -- the resolvent of the compactified process of `R (m+1)`, killed at
the exit from the image of `X m`, is `R m` -- the transported resolvents increase with `m`
(`localResolvent_le_succ`), because a path leaves the smaller domain no later and therefore
accumulates less.  Their supremum is `minimalResolvent`.

The supremum is monotone in the observable, measurable in the starting point, and sub-Markov at
every positive shift: `lam` times its value on the constant observable one is at most one
(`ofReal_mul_minimalResolvent_one_le`).  It satisfies the resolvent equation as soon as the
transported resolvents are monotone in `m`
(`minimalResolvent_resolventEquation_of_monotone`, by monotone convergence from the resolvent
equation of each member); the part-process identity enters only through that monotonicity
(`minimalResolvent_resolventEquation`).

No minimality property among resolvent families is asserted here.  The declaration names
keep the word `minimal` because the object is the resolvent of Blumenthal--Getoor's minimal
process, but that is a name and not a claim.

The regularity data of each compactification are an explicit hypothesis throughout: positivity,
contractivity and the resolvent identity do not by themselves give a compactified semigroup a
continuous-path process.

No transition semigroup, no process on the ambient space, and no conservativity are constructed
here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)













section Compatible

variable (iota : ∀ m, X m → X (m + 1))





end Compatible















section ResolventEquation

variable (iota : ∀ m, X m → X (m + 1))









end ResolventEquation

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The supremum resolvent (the minimal process of Blumenthal--Getoor, in name only)

A family of positive `C₀`-contractive resolvents `R m` on local state spaces `X m`, embedded as
an increasing family of open subsets of an ambient measurable space, is glued here at the level
of resolvents.  Each `R m` is transported to the ambient space by extending its kernel resolvent
by zero off the `m`-th domain (`localResolvent`).  Under the part-process identity of
`Killed/GluingLocal.lean` -- the resolvent of the compactified process of `R (m+1)`, killed at
the exit from the image of `X m`, is `R m` -- the transported resolvents increase with `m`
(`localResolvent_le_succ`), because a path leaves the smaller domain no later and therefore
accumulates less.  Their supremum is `minimalResolvent`.

The supremum is monotone in the observable, measurable in the starting point, and sub-Markov at
every positive shift: `lam` times its value on the constant observable one is at most one
(`ofReal_mul_minimalResolvent_one_le`).  It satisfies the resolvent equation as soon as the
transported resolvents are monotone in `m`
(`minimalResolvent_resolventEquation_of_monotone`, by monotone convergence from the resolvent
equation of each member); the part-process identity enters only through that monotonicity
(`minimalResolvent_resolventEquation`).

No minimality property among resolvent families is asserted here.  The declaration names
keep the word `minimal` because the object is the resolvent of Blumenthal--Getoor's minimal
process, but that is a name and not a claim.

The regularity data of each compactification are an explicit hypothesis throughout: positivity,
contractivity and the resolvent identity do not by themselves give a compactified semigroup a
continuous-path process.

No transition semigroup, no process on the ambient space, and no conservativity are constructed
here.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)
















namespace MarkovProcess
end MarkovProcess
open MarkovProcess
omit [MeasurableSpace alpha] in

theorem solution (m : ℕ) (lam : ℝ) (f : alpha → ℝ≥0∞) (x : alpha) :
    localResolvent R emb m lam f x ≤ minimalResolvent R emb lam f x :=
  le_iSup (fun n ↦ localResolvent R emb n lam f x) m
