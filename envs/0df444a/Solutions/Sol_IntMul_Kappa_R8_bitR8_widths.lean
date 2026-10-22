-- Prove2me | solution 1 for IntMul.Kappa.R8.bitR8_widths
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:29:50.854055+00:00
-- url     : https://prove2.me/submissions/80d057f5-c4ed-41bc-977e-cadcbf4e58af

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.Jain

private theorem widths_of_list (h : List (ℕ × ℕ)) (m : ℕ)
    (hall : h.all (fun p => decide (0 < p.1) && decide (p.1 ≤ m)) = true) :
    ∀ p ∈ h, 0 < p.1 ∧ p.1 ≤ m := by
  intro p hp
  have := List.all_eq_true.mp hall p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem solution : ∀ p ∈ bitR8, 0 < p.1 ∧ p.1 ≤ 529 := by
  apply widths_of_list
  decide +kernel
