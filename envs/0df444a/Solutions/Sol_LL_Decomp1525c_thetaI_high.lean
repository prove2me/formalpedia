-- Prove2me | solution 1 for LL_Decomp1525c.thetaI_high
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:12:23.055972+00:00
-- url     : https://prove2.me/submissions/ff455fcb-1960-464e-8a1f-4ef76211da88

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

lemma theta_two : Chebyshev.theta 2 = Real.log 2 := by
  rw [Chebyshev.theta, show ⌊(2:ℝ)⌋₊ = 2 by norm_num,
    show (Ioc 0 2).filter Nat.Prime = {2} by decide]
  simp

end S218LL

theorem solution (x u : ℝ) (hx : 6 ≤ x) (hxu : x ≤ u) (hu : u ≤ 2 * x) :
    LL_Decomp1525c.thetaI x u = max (Chebyshev.theta (min (x - 3) (2 * x - u)) - Real.log 2) 0 := by
  set k := min (x - 3) (2 * x - u) with hk
  have hk0 : 0 ≤ k := le_min (by linarith) (by linarith)
  rcases lt_or_ge k 2 with h2 | h2
  · have hle : Chebyshev.theta k ≤ Real.log 2 :=
      S218LL.theta_two ▸ Chebyshev.theta_mono h2.le
    rw [max_eq_right (by linarith), LL_Decomp1525c.thetaI]
    apply sum_eq_zero
    intro p hp
    exfalso
    simp only [LL_Decomp1525c.P1V, mem_filter, mem_Icc] at hp
    have hx3 : (0:ℝ) ≤ x - 3 := by linarith
    have hpx : (p:ℝ) ≤ x - 3 := (Nat.le_floor_iff hx3).1 hp.1.1.2
    have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hp.1.1.1
    have : (p:ℝ) ≤ k := le_min hpx (by linarith [hp.2.2])
    linarith
  · rw [S218LL.theta_split k 2 (by norm_num) h2, S218LL.theta_two, add_sub_cancel_left,
      max_eq_left (sum_nonneg fun p _ => Real.log_natCast_nonneg p), LL_Decomp1525c.thetaI,
      LL_Decomp1525c.P1V]
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    have hx3 : (0:ℝ) ≤ x - 3 := by linarith
    simp only [mem_filter, mem_Icc, mem_Ioc, not_le, show ⌊(2:ℝ)⌋₊ = 2 by norm_num]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3, h4⟩
      have hpx : (p:ℝ) ≤ x - 3 := (Nat.le_floor_iff hx3).1 h2
      refine ⟨⟨⟨by omega, (Nat.le_floor_iff hk0).2 (le_min hpx (by linarith))⟩, hp⟩, by omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
      have hpk : (p:ℝ) ≤ k := (Nat.le_floor_iff hk0).1 h2
      have hp3 : (3:ℝ) ≤ p := by exact_mod_cast h3
      refine ⟨⟨⟨h3, (Nat.le_floor_iff hx3).2 (le_trans hpk (min_le_left _ _))⟩, hp⟩, by linarith, ?_⟩
      linarith [min_le_right (x - 3) (2 * x - u)]
