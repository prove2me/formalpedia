-- Prove2me | solution 1 for MarkovProcess.brownianMotion_map_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:50:48.926062+00:00
-- url     : https://prove2.me/submissions/938bee7d-4c18-4bdc-91c1-8c80f7814c71

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
import Theorems.Thm_MarkovProcess_brownianMotion_map_incrementsMap
import Theorems.Thm_MarkovProcess_timeIncrements_succ_apply

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess



namespace FiniteOrderedTimes





































set_option warning.simp.varHead false in
/-- Every path on the empty finite index type is the canonical empty path. -/
@[simp]
theorem eq_emptyPath {α : Type*} (path : Fin 0 → α) : path = emptyPath α :=
  Subsingleton.elim _ _



end FiniteOrderedTimes

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



/-- The recursion defining the increments: the first one is measured from the base point, the
remaining ones are the increments of the tail measured from the first coordinate. -/
theorem incrementsMap_succ {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) :
    incrementsMap x path = Fin.cons (path 0 - x) (incrementsMap (path 0) (Fin.tail path)) :=
  rfl

/-- The first increment is the displacement from the base point. -/
@[simp]
theorem incrementsMap_zero_apply {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) :
    incrementsMap x path 0 = path 0 - x := rfl

/-- Every increment after the first is the difference of two consecutive coordinates. -/
theorem incrementsMap_succ_apply : ∀ {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) (i : Fin n),
    incrementsMap x path i.succ = path i.succ - path i.castSucc := by
  intro n
  induction n with
  | zero => exact fun _ _ i ↦ i.elim0
  | succ n ih =>
    intro x path i
    rw [incrementsMap_succ, Fin.cons_succ]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [incrementsMap_zero_apply]
      rfl
    · rw [ih (path 0) (Fin.tail path) j, Fin.tail, Fin.tail, ← Fin.succ_castSucc]

/-- The increments of a finite coordinate path, in closed form. -/
theorem incrementsMap_eq_cons {n : ℕ} (x : ℝ) (path : Fin (n + 1) → ℝ) :
    incrementsMap x path =
      Fin.cons (path 0 - x) (fun i : Fin n ↦ path i.succ - path i.castSucc) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [incrementsMap_zero_apply, Fin.cons_zero]
  · rw [incrementsMap_succ_apply, Fin.cons_succ]

/-- Taking increments is measurable, jointly in the base point and the path. -/
theorem measurable_incrementsMap {n : ℕ} :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦ incrementsMap p.1 p.2) := by
  cases n with
  | zero => exact measurable_pi_lambda _ fun i ↦ i.elim0
  | succ n =>
    simp_rw [incrementsMap_eq_cons]
    refine measurable_pi_iff.mpr fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero]
      fun_prop
    · simp only [Fin.cons_succ]
      fun_prop









/-- Reading a path at a finite family of times and taking increments is measurable. -/
theorem measurable_incrementsMap_eval {n : ℕ} (s : Fin n → NNReal) (x : ℝ) :
    Measurable (fun omega : ContinuousPath ℝ ↦ incrementsMap x (fun i ↦ omega (s i))) :=
  measurable_incrementsMap.comp (measurable_const.prodMk
    (measurable_pi_lambda _ fun i ↦ ContinuousPath.measurable_coordinateProcess (s i)))



end Increments

section IndependentIncrements

/-- Dropping the first coordinate of a finite coordinate path is measurable. -/
theorem measurable_finTail {n : ℕ} :
    Measurable (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.succ

/-- Dropping the first coordinate of a product of probability measures gives the product of the
remaining ones. -/
theorem map_finTail_pi {n : ℕ} (nu : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (nu i)] :
    (Measure.pi nu).map Fin.tail = Measure.pi (fun i : Fin n ↦ nu i.succ) := by
  refine (Measure.pi_eq fun A hA ↦ ?_).symm
  have hpre : (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' (Set.univ.pi A)
      = Set.univ.pi (@Fin.cons n (fun _ ↦ Set ℝ) Set.univ A) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    rw [Fin.forall_fin_succ]
    simp [Fin.tail]
  rw [Measure.map_apply measurable_finTail (MeasurableSet.univ_pi hA), hpre, Measure.pi_pi,
    Fin.prod_univ_succ]
  simp

/-- **The increments of Brownian motion over a monotone family of times are independent
centred Gaussians.** -/
theorem brownianMotion_map_increments {n : ℕ} {t : Fin (n + 1) → NNReal} (ht : Monotone t)
    (x : ℝ) :
    (brownianMotion x).map
        (fun (omega : ContinuousPath ℝ) (i : Fin n) ↦ omega (t i.succ) - omega (t i.castSucc)) =
      Measure.pi (fun i : Fin n ↦ gaussianReal 0 (t i.succ - t i.castSucc)) := by
  have hfac : (fun (omega : ContinuousPath ℝ) (i : Fin n) ↦
      omega (t i.succ) - omega (t i.castSucc)) =
      Fin.tail ∘ (fun omega ↦ incrementsMap x (fun i ↦ omega (t i))) := by
    funext omega i
    exact (incrementsMap_succ_apply x (fun j ↦ omega (t j)) i).symm
  rw [hfac, ← Measure.map_map measurable_finTail (measurable_incrementsMap_eval t x),
    brownianMotion_map_incrementsMap ht x, map_finTail_pi]
  congr 1
  funext i
  rw [timeIncrements_succ_apply ht i]







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
theorem solution (x : ℝ) (a b : NNReal) (hab : a ≤ b) :
    (brownianMotion x).map (fun omega ↦ omega b - omega a) = gaussianReal 0 (b - a) := by
  have ht : Monotone (![a, b]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := brownianMotion_map_increments (n := 1) (t := ![a, b]) ht x
  have hmeas : Measurable (fun (omega : ContinuousPath ℝ) (i : Fin 1) ↦
      omega ((![a, b] : Fin 2 → NNReal) i.succ) - omega ((![a, b] : Fin 2 → NNReal) i.castSucc)) :=
    measurable_pi_lambda _ fun i ↦
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
  have hproj := congrArg (fun mu : Measure (Fin 1 → ℝ) ↦ mu.map (Function.eval (0 : Fin 1))) h
  have hpres := measurePreserving_eval (fun i : Fin 1 ↦ gaussianReal 0
    ((![a, b] : Fin 2 → NNReal) i.succ - (![a, b] : Fin 2 → NNReal) i.castSucc)) 0
  rw [Measure.map_map (measurable_pi_apply _) hmeas, hpres.map_eq] at hproj
  exact hproj
