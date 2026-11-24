-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_negative_grid_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:37:37.437839+00:00
-- url     : https://prove2.me/submissions/415daa14-17f9-4503-947e-3be9a772c175


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
/-- Independent increment reduction. -/
theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
      (t : ℝ≥0) (a c : ℝ) (n : ℕ),
      X 0 ω = 0 → -a ≤ X ((n:ℝ≥0)*t) ω → (n:ℝ)*c < -a →
      (∏ i : Fin n, (if X (((i.val+1 : ℕ):ℝ≥0)*t) ω -
        X ((i.val:ℝ≥0)*t) ω < c then (1:ℝ) else 0)) = 0 := by
  intro Ω X ω t a c n hzero hterm hn
  let f : ℕ → ℝ := fun j => X ((j:ℝ≥0)*t) ω
  have htel : ∀ k : ℕ, (∑ j ∈ Finset.range k, (f (j+1)-f j)) = f k-f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih]; ring
  by_contra hne
  have hall (i : Fin n) : f (i.val+1)-f i.val ≤ c := by
    by_contra! hi
    apply hne
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hnot : ¬ f (i.val+1)-f i.val < c := not_lt_of_ge hi.le
    change (if f (i.val+1)-f i.val<c then (1:ℝ) else 0)=0
    simp [hnot]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => hall i)
  rw [Fin.sum_univ_eq_sum_range (fun j => f (j+1)-f j) n, htel n] at hsum
  simp [f,hzero] at hsum
  linarith
