-- Prove2me | solution 1 for KernelRank.iterate_sum_shiftDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:31:50.77467+00:00
-- url     : https://prove2.me/submissions/154ea619-82b3-4c0e-a9b3-7e026b5a5105

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_sum_shiftDeriv_eq_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {S : Finset ℂ} {P : ℂ → ℂ[X]} (a : ℂ) (n : ℕ)
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) :
    ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly ((shiftDeriv a μ)^[n] (P μ)) μ u = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact sum_shiftDeriv_eq_zero a ih
end KernelRank
