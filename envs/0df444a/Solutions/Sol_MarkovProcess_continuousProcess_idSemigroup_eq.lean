-- Prove2me | solution 1 for MarkovProcess.continuousProcess_idSemigroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:27:48.318996+00:00
-- url     : https://prove2.me/submissions/3a4616a3-0a8e-480b-b0b9-338582b439ad

import Definitions.Def_MarkovProcess_V3H_Examples_Identity_d8db12c8
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
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
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The identity semigroup and its continuous-path process

The transition semigroup that never moves: `idSemigroup t = Kernel.id` at every time.  It is
conservative, Feller, and satisfies the Kolmogorov moment criterion with exponents `p = 1`,
`q = 2` and constant `M = 0`, so the existence-and-uniqueness theorem of `MarkovProcess.Main`
applies to it verbatim.  The resulting process is identified: from every starting point `x` its
law is the Dirac mass at the constant path at `x`.

This file witnesses that the hypotheses of the main theorem are jointly satisfiable; it proves
nothing about any other semigroup, and it makes no claim about a semigroup that actually moves
(see `MarkovProcess.Examples.Drift` for that).
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

section Definition

variable {alpha : Type*} [MeasurableSpace alpha]







end Definition

section Feller

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





variable [LocallyCompactSpace alpha]



end Feller

section Moments

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The identity semigroup satisfies the Kolmogorov moment criterion with `p = 1`, `q = 2` and
vanishing constant: the displacement over any time is identically zero. -/
theorem hasKolmogorovMoments_idSemigroup :
    (idSemigroup (alpha := alpha)).HasKolmogorovMoments 1 2 0 := by
  refine ⟨one_pos, one_lt_two, fun h y ↦ ?_⟩
  have hmeas : Measurable (fun z : alpha ↦ edist z y ^ (1 : ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 1
  rw [idSemigroup_apply h y, lintegral_dirac' y hmeas, edist_self,
    ENNReal.zero_rpow_of_pos one_pos, ENNReal.coe_zero, zero_mul]

end Moments

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [Nonempty alpha]

omit [LocallyCompactSpace alpha] in
/-- The identity semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_idSemigroup :
    (idSemigroup (alpha := alpha)).KolmogorovRegular isConservative_idSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_idSemigroup hasKolmogorovMoments_idSemigroup



omit [LocallyCompactSpace alpha] in
private theorem ae_eq_const_of_continuousProcess_idSemigroup (x : alpha) :
    (fun omega : ContinuousPath alpha ↦ omega) =ᵐ[
      SubMarkovKernelSemigroup.IsConservative.continuousProcess (idSemigroup (alpha := alpha))
        isConservative_idSemigroup x]
      fun _ ↦ ContinuousMap.const NNReal x := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    (idSemigroup (alpha := alpha)) isConservative_idSemigroup x with hmu
  have hcoord : ∀ q : DenseTime, ∀ᵐ omega ∂mu,
      omega (DenseTime.castOrderEmbedding q) = x := by
    intro q
    have hmeas : Measurable
        (fun omega : ContinuousPath alpha ↦ omega (DenseTime.castOrderEmbedding q)) :=
      ContinuousPath.measurable_coordinateProcess (alpha := alpha) _
    have hmap := SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_eval
      (idSemigroup (alpha := alpha)) isConservative_idSemigroup kolmogorovRegular_idSemigroup q
    have hmapx : Measure.map (fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) mu = Measure.dirac x := by
      rw [hmu, ← Kernel.map_apply _ hmeas, hmap, idSemigroup_apply]
    have hsingleton : MeasurableSet ({x}ᶜ : Set alpha) :=
      (isClosed_singleton (x := x)).measurableSet.compl
    have hzero : mu ((fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) ⁻¹' ({x}ᶜ : Set alpha)) = 0 := by
      rw [← Measure.map_apply hmeas hsingleton, hmapx, Measure.dirac_apply' x hsingleton,
        Set.indicator_of_notMem (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
          not_true_eq_false, not_false_eq_true])]
    exact hzero
  have hall : ∀ᵐ omega ∂mu, ∀ q : DenseTime,
      omega (DenseTime.castOrderEmbedding q) = x := ae_all_iff.mpr hcoord
  filter_upwards [hall] with omega homega
  apply ContinuousPath.denseRestriction_injective
  funext q
  rw [ContinuousPath.denseRestriction_apply, ContinuousPath.denseRestriction_apply, homega q]
  rfl



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
# The identity semigroup and its continuous-path process

The transition semigroup that never moves: `idSemigroup t = Kernel.id` at every time.  It is
conservative, Feller, and satisfies the Kolmogorov moment criterion with exponents `p = 1`,
`q = 2` and constant `M = 0`, so the existence-and-uniqueness theorem of `MarkovProcess.Main`
applies to it verbatim.  The resulting process is identified: from every starting point `x` its
law is the Dirac mass at the constant path at `x`.

This file witnesses that the hypotheses of the main theorem are jointly satisfiable; it proves
nothing about any other semigroup, and it makes no claim about a semigroup that actually moves
(see `MarkovProcess.Examples.Drift` for that).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty







variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [Nonempty alpha]







namespace MarkovProcess
end MarkovProcess
open MarkovProcess
omit [LocallyCompactSpace alpha] in

theorem solution (x : alpha) :
    SubMarkovKernelSemigroup.IsConservative.continuousProcess (idSemigroup (alpha := alpha))
        isConservative_idSemigroup x =
      Measure.dirac (ContinuousMap.const NNReal x) := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    (idSemigroup (alpha := alpha)) isConservative_idSemigroup x with hmu
  have hprob : IsProbabilityMeasure mu := by
    rw [hmu]
    infer_instance
  calc mu = mu.map id := (Measure.map_id).symm
    _ = mu.map (fun _ ↦ ContinuousMap.const NNReal x) :=
        Measure.map_congr (ae_eq_const_of_continuousProcess_idSemigroup x)
    _ = mu Set.univ • Measure.dirac (ContinuousMap.const NNReal x) := Measure.map_const _ _
    _ = Measure.dirac (ContinuousMap.const NNReal x) := by
        rw [measure_univ, one_smul]
