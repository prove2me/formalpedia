-- Prove2me | solution 1 for OAI.SevenEighths.EulerFactors.factor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:52:20.21839+00:00
-- url     : https://prove2.me/submissions/f0661bfa-e5e1-488b-aaa2-be736ddf0254

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_EulerFactors
import Theorems.Thm_OAI_SevenEighths_EulerFactors_norm_term_lt_one

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.EulerFactors
noncomputable section
namespace OAI.SevenEighths.EulerFactors
theorem _root_.solution {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)
end OAI.SevenEighths.EulerFactors
