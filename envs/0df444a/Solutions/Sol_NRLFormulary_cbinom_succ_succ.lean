-- Prove2me | solution 1 for NRLFormulary.cbinom_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:31:06.324521+00:00
-- url     : https://prove2.me/submissions/57e4648f-cc4f-4824-ac14-f57d1f0144d6

import Mathlib
import Definitions.Def_NRLFormulary_cbinom

open NRLFormulary

theorem solution (w : ℂ) (k : ℕ) :
    cbinom (w + 1) (k + 1) = cbinom w k + cbinom w (k + 1) := by
  unfold cbinom
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  have h1 : ∏ j ∈ Finset.range k, (w + 1 - ((j + 1 : ℕ) : ℂ)) = ∏ j ∈ Finset.range k, (w - (j : ℂ)) := by
    refine Finset.prod_congr rfl (fun j _ => ?_); push_cast; ring
  rw [h1, Nat.factorial_succ]
  have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast at hk ⊢
  field_simp
  ring
