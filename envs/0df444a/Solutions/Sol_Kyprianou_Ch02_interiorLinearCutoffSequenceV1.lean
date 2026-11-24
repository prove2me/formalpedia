-- Prove2me | solution 1 for Kyprianou.Ch02.interiorLinearCutoffSequenceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:12:46.154811+00:00
-- url     : https://prove2.me/submissions/9ef670f8-955f-4b82-a9f2-1bb77366bfd6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_interiorLinearRampBoundsV1
import Theorems.Thm_Kyprianou_Ch02_interiorLinearRampTendstoV1
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (r : ℝ) (hr : 0 < r) :
    ∃ f : ℕ → BoundedContinuousFunction ℝ ℝ,
      (∀ n x, 0 ≤ f n x) ∧
      (∀ n x, f n x ≤ (Set.Ioo (0 : ℝ) r).indicator id x) ∧
      (∀ n, ∃ δ > 0, ∀ x, |x| < δ → f n x = 0) ∧
      ∀ x, Tendsto (fun n => f n x) atTop
        (nhds ((Set.Ioo (0 : ℝ) r).indicator id x)) := by
  let g (n : ℕ) (x : ℝ) : ℝ :=
    min (max 0 (x - 1 / ((n : ℝ) + 1))) (max 0 (((n : ℝ) + 1) * (r - x)))
  have hb (n : ℕ) (x : ℝ) := Kyprianou.Ch02.interiorLinearRampBoundsV1 r hr n x
  let f (n : ℕ) : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨g n, by unfold g; fun_prop⟩ r (by
        intro x y
        change dist (g n x) (g n y) ≤ r
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [(hb n x).1, (hb n y).1, (hb n x).2.2.1, (hb n y).2.2.1])
  refine ⟨f, fun n x => (hb n x).1, fun n x => (hb n x).2.1, ?_, ?_⟩
  · intro n
    exact ⟨1 / ((n : ℝ) + 1), by positivity, fun x => (hb n x).2.2.2⟩
  · intro x
    exact Kyprianou.Ch02.interiorLinearRampTendstoV1 r hr x
