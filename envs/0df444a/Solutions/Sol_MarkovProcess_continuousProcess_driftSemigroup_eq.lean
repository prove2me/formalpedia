-- Prove2me | solution 1 for MarkovProcess.continuousProcess_driftSemigroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:43:53.370322+00:00
-- url     : https://prove2.me/submissions/09dc86f5-557a-4b42-936a-9619eb7e84f2

import Definitions.Def_MarkovProcess_V3H_Examples_Drift_f1e2d4e2
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
import Theorems.Thm_MarkovProcess_hasKolmogorovMoments_driftSemigroup

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Definition









end Definition

section Feller











end Feller

section Moments



end Moments

section Process

/-- The drift semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_driftSemigroup (v : E) :
    (driftSemigroup v).KolmogorovRegular (isConservative_driftSemigroup v) :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    (isConservative_driftSemigroup v) (hasKolmogorovMoments_driftSemigroup v)





omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The straight line, evaluated at a time. -/
@[simp]
theorem driftPath_apply (v : E) (x : E) (t : NNReal) :
    driftPath v x t = x + (t : ℝ) • v := rfl

private theorem ae_eq_driftPath (v : E) (x : E) :
    (fun omega : ContinuousPath E ↦ omega) =ᵐ[
      SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
        (isConservative_driftSemigroup v) x]
      fun _ ↦ driftPath v x := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
    (isConservative_driftSemigroup v) x with hmu
  have hcoord : ∀ q : DenseTime, ∀ᵐ omega ∂mu,
      omega (DenseTime.castOrderEmbedding q) = driftPath v x (DenseTime.castOrderEmbedding q) := by
    intro q
    have hmeas : Measurable
        (fun omega : ContinuousPath E ↦ omega (DenseTime.castOrderEmbedding q)) :=
      ContinuousPath.measurable_coordinateProcess (alpha := E) _
    have hmap := SubMarkovKernelSemigroup.IsConservative.continuousProcess_map_eval
      (driftSemigroup v) (isConservative_driftSemigroup v) (kolmogorovRegular_driftSemigroup v) q
    have hmapx : Measure.map (fun omega : ContinuousPath E ↦
        omega (DenseTime.castOrderEmbedding q)) mu =
        Measure.dirac (driftPath v x (DenseTime.castOrderEmbedding q)) := by
      rw [hmu, ← Kernel.map_apply _ hmeas, hmap, driftSemigroup_apply, driftPath_apply]
    set y := driftPath v x (DenseTime.castOrderEmbedding q) with hy
    have hsingleton : MeasurableSet ({y}ᶜ : Set E) :=
      (isClosed_singleton (x := y)).measurableSet.compl
    show mu ((fun omega : ContinuousPath E ↦
      omega (DenseTime.castOrderEmbedding q)) ⁻¹' ({y}ᶜ : Set E)) = 0
    rw [← Measure.map_apply hmeas hsingleton, hmapx, Measure.dirac_apply' y hsingleton,
      Set.indicator_of_notMem (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
        not_true_eq_false, not_false_eq_true])]
  have hall : ∀ᵐ omega ∂mu, ∀ q : DenseTime,
      omega (DenseTime.castOrderEmbedding q) =
        driftPath v x (DenseTime.castOrderEmbedding q) := ae_all_iff.mpr hcoord
  filter_upwards [hall] with omega homega
  apply ContinuousPath.denseRestriction_injective
  funext q
  rw [ContinuousPath.denseRestriction_apply, ContinuousPath.denseRestriction_apply, homega q]



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
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]















namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (v : E) (x : E) :
    SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
        (isConservative_driftSemigroup v) x =
      Measure.dirac (driftPath v x) := by
  set mu := SubMarkovKernelSemigroup.IsConservative.continuousProcess (driftSemigroup v)
    (isConservative_driftSemigroup v) x with hmu
  have hprob : IsProbabilityMeasure mu := by
    rw [hmu]
    infer_instance
  calc mu = mu.map id := (Measure.map_id).symm
    _ = mu.map (fun _ ↦ driftPath v x) := Measure.map_congr (ae_eq_driftPath v x)
    _ = mu Set.univ • Measure.dirac (driftPath v x) := Measure.map_const _ _
    _ = Measure.dirac (driftPath v x) := by rw [measure_univ, one_smul]
