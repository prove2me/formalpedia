-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.progressivelyMeasurable_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:39:03.424983+00:00
-- url     : https://prove2.me/submissions/8c37821d-9f02-42ba-8bfc-37853d247ae6

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F001
import Definitions.Def_LevyStochCalc_Ito_JumpTelescope_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Cells of a stopping time and a simple random mark

A random mark taking finitely many values, together with a stopping time taking finitely many
deterministic values below a horizon, decomposes the sample space into the cells on which both
are constant. The indicator of such a cell is bounded by one and, when the cell is known at the
deterministic time the stopping time takes there, it is measurable at that time; summing the
indicators against a function of the mark recovers that function read along the mark.
Consequently the increment of an integrand read along the mark between two stopping times is the
finite sum of the cell integrands, each of which is a bounded weight vanishing before the
deterministic time of its cell times an increment vanishing up to that time, hence progressively
measurable with finite energy on bounded windows.

## Main statements

* `LevyStochCalc.Brownian.Ito.cellWeight` — the indicator of a cell of the decomposition.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_weight_mul_stopped_sub` — a bounded weight
  known at a deterministic time, times an increment vanishing up to that time, is progressively
  measurable.
* `LevyStochCalc.Brownian.Ito.stopped_sub_eq_sum_cells` — the increment of an integrand read
  along a simple random mark is the sum of its cell integrands.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_simple` — that increment is
  progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellWeight

variable {Ω : Type u} {α : Type*}

variable (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeight

section CellWeightMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeightMeasurable

section CellWeightSum

variable {Ω : Type u} {α : Type*} (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

end CellWeightSum

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

end Weight

section WeightEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

end WeightEnergy

section CellFamily

variable {Ω : Type u} {α : Type*} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

end CellFamily

section CellFamilyProgressive

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}



theorem _root_.solution {ι : Type*}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (A : ι → Ω → ℝ → ℝ)
    (hA : ∀ i, Probability.ProgressivelyMeasurable ℱ (A i)) (s : Finset ι) :
    Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ s, A i ω u := by
  classical
  intro t
  have he : (fun p : Ω × ℝ => (Set.Iic t).indicator
      (fun u => ∑ i ∈ s, A i p.1 u) p.2) =
      (fun p : Ω × ℝ => ∑ i ∈ s, (Set.Iic t).indicator (A i p.1) p.2) := by
    funext p
    by_cases hp : p.2 ≤ t <;> simp [Set.indicator_apply, hp]
  rw [he]
  clear he
  induction s using Finset.induction_on with
  | empty => simpa using (stronglyMeasurable_const (b := (0 : ℝ)))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hA i t).add ih
