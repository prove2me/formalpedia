-- Prove2me | solution 1 for Kyprianou.Ch02.boundedContinuousNegativeCutoffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:57:10.913136+00:00
-- url     : https://prove2.me/submissions/351e35f9-bf2e-4d80-b3fe-eb512f8a258f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    (r : ℝ) (hr : 0 < r) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      (∀ x : ℝ, 0 ≤ f x) ∧
      (∀ x : ℝ, -r ≤ x → f x = 0) ∧
      ∀ x : ℝ, x < -r → 0 < f x := by
  let g : ℝ → ℝ := fun x => max 0 (min 1 (-x-r))
  have hg0 (x : ℝ) : 0 ≤ g x := le_max_left _ _
  have hg1 (x : ℝ) : g x ≤ 1 := max_le zero_le_one (min_le_left _ _)
  let f : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨g, by dsimp [g]; fun_prop⟩ 1
      (fun x y => by
        change dist (g x) (g y) ≤ 1
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [hg0 x, hg1 x, hg0 y, hg1 y])
  refine ⟨f, hg0, ?_, ?_⟩
  · intro x hx
    change max 0 (min 1 (-x-r)) = 0
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  · intro x hx
    change 0 < max 0 (min 1 (-x-r))
    exact (lt_min zero_lt_one (by linarith)).trans_le (le_max_right _ _)
