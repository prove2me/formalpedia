-- Prove2me | solution 1 for KernelRank.eq_zero_of_iterate_shiftDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:31:38.442678+00:00
-- url     : https://prove2.me/submissions/ac4168b8-3e62-441a-8254-b9256f4f18fa

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_eq_zero_of_shiftDeriv_eq_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {a μ : ℂ} (hμ : μ ≠ a) (n : ℕ) {P : ℂ[X]}
    (h : (shiftDeriv a μ)^[n] P = 0) : P = 0 := by
  induction n generalizing P with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact eq_zero_of_shiftDeriv_eq_zero hμ (ih h)
end KernelRank
