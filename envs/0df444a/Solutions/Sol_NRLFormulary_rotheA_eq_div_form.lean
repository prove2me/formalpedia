-- Prove2me | solution 1 for NRLFormulary.rotheA_eq_div_form
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:32:45.276963+00:00
-- url     : https://prove2.me/submissions/2f1ebf2e-a867-44a5-bb96-9e0c0eb4132b

import Mathlib
import Definitions.Def_NRLFormulary_cbinom
import Definitions.Def_NRLFormulary_rotheA

open NRLFormulary

theorem solution (x z : ℂ) (k : ℕ) (h : x + (k : ℂ) * z ≠ 0) :
    rotheA x z k = x / (x + (k : ℂ) * z) * cbinom (x + (k : ℂ) * z) k := by
  cases k with
  | zero =>
    simp at h
    simp [rotheA, cbinom, h]
  | succ k =>
    rw [rotheA, cbinom, Finset.prod_range_succ']
    have h1 : ∏ j ∈ Finset.range k, (x + ((k + 1 : ℕ) : ℂ) * z - ((j + 1 : ℕ) : ℂ))
        = ∏ j ∈ Finset.range k, (x + ((k : ℂ) + 1) * z - ((j : ℂ) + 1)) := by
      refine Finset.prod_congr rfl (fun j _ => ?_); push_cast; ring
    rw [h1]
    simp only [Nat.cast_zero, sub_zero]
    have h' : x + z * ((k + 1 : ℕ) : ℂ) ≠ 0 := by rwa [mul_comm] at h
    field_simp
