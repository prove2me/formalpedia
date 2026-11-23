-- Prove2me | solution 1 for Kyprianou.Ch02.absSummableJumpSeriesMonotonePairV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:46:52.221532+00:00
-- url     : https://prove2.me/submissions/d35fb008-dddc-418a-b87f-6207bc353c9c

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-
The constructive positive/negative sum argument is adapted from StochLean
(PathVariation, Apache-2.0, StochLean contributors). All proof checking is remote.
-/
theorem solution
    (g : ℝ≥0 → ℝ)
    (hs : ∀ T : ℝ≥0, Summable
      (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|)) :
    ∃ (p q : ℝ≥0 → ℝ), Monotone p ∧ Monotone q ∧
      ∀ T : ℝ≥0,
        (∑' s : Set.Ioc (0 : ℝ≥0) T, g s) = p T - q T := by
  let pos : ℝ≥0 → ℝ := fun s => (|g s| + g s) / 2
  let neg : ℝ≥0 → ℝ := fun s => (|g s| - g s) / 2
  have hpos (T : ℝ≥0) :
      Summable (fun s : Ioc 0 T => pos s) :=
    ((hs T).add (hs T).of_abs).div_const 2
  have hneg (T : ℝ≥0) :
      Summable (fun s : Ioc 0 T => neg s) :=
    ((hs T).sub (hs T).of_abs).div_const 2
  have hpos0 (s : ℝ≥0) : 0 ≤ pos s := by
    have h := neg_abs_le (g s)
    dsimp only [pos]
    linarith only [h]
  have hneg0 (s : ℝ≥0) : 0 ≤ neg s := by
    have h := le_abs_self (g s)
    dsimp only [neg]
    linarith only [h]
  have hposm : Monotone (fun T : ℝ≥0 => ∑' s : Ioc 0 T, pos s) := by
    intro t u htu
    let hsub : Ioc (0 : ℝ≥0) t ⊆ Ioc 0 u :=
      fun _ hs => ⟨hs.1, hs.2.trans htu⟩
    exact (hpos t).tsum_le_tsum_of_inj (Set.inclusion hsub)
      (Set.inclusion_injective hsub)
      (fun s _ => hpos0 s) (fun _ => le_rfl) (hpos u)
  have hnegm : Monotone (fun T : ℝ≥0 => ∑' s : Ioc 0 T, neg s) := by
    intro t u htu
    let hsub : Ioc (0 : ℝ≥0) t ⊆ Ioc 0 u :=
      fun _ hs => ⟨hs.1, hs.2.trans htu⟩
    exact (hneg t).tsum_le_tsum_of_inj (Set.inclusion hsub)
      (Set.inclusion_injective hsub)
      (fun s _ => hneg0 s) (fun _ => le_rfl) (hneg u)
  refine ⟨_, _, hposm, hnegm, ?_⟩
  intro T
  symm
  rw [← (hpos T).tsum_sub (hneg T)]
  apply tsum_congr
  intro s
  dsimp only [pos, neg]
  ring
