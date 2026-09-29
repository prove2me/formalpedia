-- Prove2me | solution 1 for Hirsch.larman_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:56:28.543142+00:00
-- url     : https://prove2.me/submissions/6311d213-a5e7-4ede-818f-c078d5e01ce9

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_dimension_three_bound
import Theorems.Thm_Hirsch_larman_high_dimension

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) := by
  by_cases hd : d ≤ 3
  · have h := Hirsch.dimension_three_bound d n hd a b hne hbd
    have he : n * 2 ^ (d - 3) = n := by simp [Nat.sub_eq_zero_of_le hd]
    rw [he]
    intro u hu v hv
    obtain ⟨w, hw0, hwend, hstep⟩ := h u hu v hv
    refine ⟨fun i => w (min i (n - d)), by simpa using hw0, ?_, ?_⟩
    · simpa [Nat.min_eq_right (Nat.sub_le n d)] using hwend
    · intro i hi
      by_cases hid : i < n - d
      · simpa only [Nat.min_eq_left hid.le, Nat.min_eq_left (Nat.succ_le_of_lt hid)]
          using hstep i hid
      · simp [Nat.min_eq_right (by omega : n - d ≤ i),
          Nat.min_eq_right (by omega : n - d ≤ i + 1)]
  · exact Hirsch.larman_high_dimension d n (by omega) a b hne hbd

#print axioms solution
