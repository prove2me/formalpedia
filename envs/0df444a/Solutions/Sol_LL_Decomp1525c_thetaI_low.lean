-- Prove2me | solution 1 for LL_Decomp1525c.thetaI_low
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:11:42.098989+00:00
-- url     : https://prove2.me/submissions/e1e70f45-803c-4aee-93b3-9926c6976e48

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI

open Finset

namespace S218LL

/-- θ splits at a lower threshold `m ≤ y`. -/
lemma theta_split (y m : ℝ) (hm0 : 0 ≤ m) (hmy : m ≤ y) :
    Chebyshev.theta y = Chebyshev.theta m +
      ∑ p ∈ ((Ioc 0 ⌊y⌋₊).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊m⌋₊), Real.log p := by
  rw [Chebyshev.theta, Chebyshev.theta, ← sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊m⌋₊)]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  have := Nat.floor_le_floor (a := m) (b := y) hmy
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, le_trans h2 this⟩, h3⟩, h2⟩

end S218LL

theorem solution (x u : ℝ) (hx : 6 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    LL_Decomp1525c.thetaI x u = Chebyshev.theta (x - 3) - Chebyshev.theta (max (x - u) 2) := by
  set m := max (x - u) 2 with hm
  have hm0 : 0 ≤ m := le_trans (by norm_num) (le_max_right _ _)
  have hmy : m ≤ x - 3 := max_le (by linarith) (by linarith)
  rw [S218LL.theta_split (x - 3) m hm0 hmy, add_sub_cancel_left, LL_Decomp1525c.thetaI,
    LL_Decomp1525c.P1V]
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  have hx3 : (0:ℝ) ≤ x - 3 := by linarith
  simp only [mem_filter, mem_Icc, mem_Ioc, not_le]
  rw [Nat.floor_lt hm0]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3, h4⟩
    refine ⟨⟨⟨by omega, h2⟩, hp⟩, max_lt (by linarith) ?_⟩
    exact_mod_cast (show 2 < p by omega)
  · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
    have hp2 : (2:ℝ) < p := lt_of_le_of_lt (le_max_right _ _) h3
    have hp3 : 3 ≤ p := by exact_mod_cast (show (2:ℝ) < p from hp2)
    have hpx : (p:ℝ) ≤ x - 3 := (Nat.le_floor_iff hx3).1 h2
    exact ⟨⟨⟨hp3, h2⟩, hp⟩, by linarith [le_max_left (x - u) 2], by linarith⟩
