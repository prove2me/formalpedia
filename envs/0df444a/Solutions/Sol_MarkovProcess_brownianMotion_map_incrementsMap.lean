-- Prove2me | solution 1 for MarkovProcess.brownianMotion_map_incrementsMap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:44:48.720277+00:00
-- url     : https://prove2.me/submissions/abe7c457-6b31-4a17-9adc-a8c2dd18abee

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Examples_BrownianMotion_c88465db
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Theorems.Thm_MarkovProcess_brownianMotion_map_prodMk_shift

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





/-- The first time increment is the first time itself. -/
@[simp]
theorem timeIncrements_zero_apply {n : ℕ} (s : Fin (n + 1) → NNReal) :
    timeIncrements s 0 = s 0 := rfl



/-- Reading a path at a finite family of times and taking increments is measurable. -/
theorem measurable_incrementsMap_eval {n : ℕ} (s : Fin n → NNReal) (x : ℝ) :
    Measurable (fun omega : ContinuousPath ℝ ↦ incrementsMap x (fun i ↦ omega (s i))) :=
  measurable_incrementsMap.comp (measurable_const.prodMk
    (measurable_pi_lambda _ fun i ↦ ContinuousPath.measurable_coordinateProcess (s i)))



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
theorem solution : ∀ {n : ℕ} {s : Fin n → NNReal}, Monotone s → ∀ x : ℝ,
    (brownianMotion x).map (fun omega ↦ incrementsMap x (fun i ↦ omega (s i))) =
      Measure.pi (fun i ↦ gaussianReal 0 (timeIncrements s i)) := by
  intro n
  induction n with
  | zero =>
    intro s _ x
    have : IsProbabilityMeasure ((brownianMotion x).map
        (fun omega ↦ incrementsMap x (fun i ↦ omega (s i)))) :=
      Measure.isProbabilityMeasure_map (measurable_incrementsMap_eval s x).aemeasurable
    exact (Measure.pi_eq fun A _ ↦ by simp).symm
  | succ n ih =>
    intro s hs x
    have hs' : Monotone (fun i : Fin n ↦ s i.succ - s 0) := fun a b hab ↦
      tsub_le_tsub_right (hs (Fin.succ_le_succ_iff.mpr hab)) _
    have hPhi : Measurable (fun p : ℝ × ContinuousPath ℝ ↦
        @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
          (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) := by
      refine measurable_finCons.comp ((measurable_fst.sub measurable_const).prodMk ?_)
      exact measurable_incrementsMap.comp (measurable_fst.prodMk
        (measurable_pi_lambda _ fun i ↦
          (ContinuousPath.measurable_coordinateProcess (s i.succ - s 0)).comp measurable_snd))
    have hpair : Measurable (fun omega : ContinuousPath ℝ ↦
        (omega (s 0), ContinuousPath.shift (s 0) omega)) :=
      (ContinuousPath.measurable_coordinateProcess (s 0)).prodMk
        (ContinuousPath.measurable_shift_fixed (s 0))
    have hfactor : (fun omega : ContinuousPath ℝ ↦ incrementsMap x (fun i ↦ omega (s i))) =
        (fun p : ℝ × ContinuousPath ℝ ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
              (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ∘
          (fun omega ↦ (omega (s 0), ContinuousPath.shift (s 0) omega)) := by
      funext omega
      have harg : (fun i : Fin n ↦ (ContinuousPath.shift (s 0) omega) (s i.succ - s 0)) =
          Fin.tail (fun i ↦ omega (s i)) := by
        funext i
        show omega (s 0 + (s i.succ - s 0)) = omega (s i.succ)
        rw [add_tsub_cancel_of_le (hs (Fin.zero_le _))]
      show incrementsMap x (fun i ↦ omega (s i)) =
        Fin.cons (omega (s 0) - x)
          (incrementsMap (omega (s 0))
            (fun i : Fin n ↦ (ContinuousPath.shift (s 0) omega) (s i.succ - s 0)))
      rw [incrementsMap_succ, harg]
    rw [hfactor, ← Measure.map_map hPhi hpair, brownianMotion_map_prodMk_shift]
    refine (Measure.pi_eq fun A hA ↦ ?_).symm
    have hpiA : MeasurableSet (Set.univ.pi A) := MeasurableSet.univ_pi hA
    rw [Measure.map_apply hPhi hpiA, Measure.compProd_apply (hPhi hpiA)]
    have hsplit : ∀ y : ℝ, brownianMotion y (Prod.mk y ⁻¹'
          ((fun p : ℝ × ContinuousPath ℝ ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
              (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
        Set.indicator ((fun u : ℝ ↦ u - x) ⁻¹' (A 0))
          (fun _ ↦ ∏ i : Fin n,
            gaussianReal 0 (timeIncrements (fun i : Fin n ↦ s i.succ - s 0) i) (A i.succ)) y := by
      intro y
      have hmem : ∀ eta : ContinuousPath ℝ,
          (Prod.mk y eta ∈ ((fun p : ℝ × ContinuousPath ℝ ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
                (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) ↔
            (y - x ∈ A 0 ∧
              incrementsMap y (fun i : Fin n ↦ eta (s i.succ - s 0)) ∈
                Set.univ.pi (fun i : Fin n ↦ A i.succ)) := by
        intro eta
        simp only [Set.mem_preimage, Set.mem_univ_pi]
        rw [Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases hy : y - x ∈ A 0
      · have hy' : y ∈ (fun u : ℝ ↦ u - x) ⁻¹' (A 0) := hy
        rw [Set.indicator_of_mem hy']
        have hset : (Prod.mk y ⁻¹'
            ((fun p : ℝ × ContinuousPath ℝ ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
                (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
            (fun eta : ContinuousPath ℝ ↦
              incrementsMap y (fun i : Fin n ↦ eta (s i.succ - s 0))) ⁻¹'
              (Set.univ.pi (fun i : Fin n ↦ A i.succ)) := by
          ext eta
          rw [Set.mem_preimage, hmem eta]
          simp only [Set.mem_preimage, hy, true_and]
        rw [hset, ← Measure.map_apply
          (measurable_incrementsMap_eval (fun i : Fin n ↦ s i.succ - s 0) y)
          (MeasurableSet.univ_pi fun i ↦ hA i.succ), ih hs' y, Measure.pi_pi]
      · have hy' : y ∉ (fun u : ℝ ↦ u - x) ⁻¹' (A 0) := hy
        rw [Set.indicator_of_notMem hy']
        have hset : (Prod.mk y ⁻¹'
            ((fun p : ℝ × ContinuousPath ℝ ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) (p.1 - x)
                (incrementsMap p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
            (∅ : Set (ContinuousPath ℝ)) := by
          ext eta
          rw [Set.mem_preimage, hmem eta]
          simp only [Set.mem_empty_iff_false, iff_false, not_and, hy, IsEmpty.forall_iff]
        rw [hset, measure_empty]
    have hsub : Measurable (fun u : ℝ ↦ u - x) := by fun_prop
    simp_rw [hsplit]
    rw [lintegral_indicator (hsub (hA 0)), setLIntegral_const,
      ← Measure.map_apply hsub (hA 0),
      gaussianReal_map_sub_const x, sub_self, Fin.prod_univ_succ, timeIncrements_zero_apply]
    exact mul_comm _ _
