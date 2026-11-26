-- Prove2me | solution 1 for Kyprianou.Ch04.disjointIndicatorSumSquare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:43:26.777885+00:00
-- url     : https://prove2.me/submissions/392b3832-cbbf-4a6c-88f8-bcc1eac2ec44

import Mathlib
open scoped BigOperators
set_option autoImplicit false
universe u v

/-- Squaring a disjoint finite indicator sum squares each coefficient separately. -/
theorem solution
    {A : Type u} {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (B : ι → Set A) (c : ι → ℝ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (x : A) :
    (∑ i ∈ s, (B i).indicator (fun _ => c i) x)^2 =
      ∑ i ∈ s, (B i).indicator (fun _ => (c i)^2) x := by
  classical
  by_cases hx : ∃ i ∈ s, x ∈ B i
  · obtain ⟨i, hi, hxi⟩ := hx
    have hnot (j : ι) (hj : j ∈ s) (hji : j ≠ i) : x ∉ B j :=
      fun hxj => Set.disjoint_left.mp (hd i hi j hj hji.symm) hxi hxj
    rw [Finset.sum_eq_single_of_mem i hi, Finset.sum_eq_single_of_mem i hi]
    · simp [Set.indicator_of_mem hxi]
    · intro j hj hji
      simp [Set.indicator_of_notMem (hnot j hj hji)]
    · intro j hj hji
      simp [Set.indicator_of_notMem (hnot j hj hji)]
  · have hnot (i : ι) (hi : i ∈ s) : x ∉ B i :=
      fun hxi => hx ⟨i, hi, hxi⟩
    have h₁ : (∑ i ∈ s, (B i).indicator (fun _ => c i) x) = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hnot i hi) _
    have h₂ : (∑ i ∈ s, (B i).indicator (fun _ => (c i)^2) x) = 0 :=
      Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hnot i hi) _
    rw [h₁, h₂]
    norm_num
