-- Prove2me | solution 1 for OAI.SevenEighths.EulerFactors.differentiable_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:51:45.242071+00:00
-- url     : https://prove2.me/submissions/f7032a8b-f78b-44eb-b7eb-8aaf317462f4

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_EulerFactors

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.EulerFactors
noncomputable section
namespace OAI.SevenEighths.EulerFactors
theorem _root_.solution {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))
end OAI.SevenEighths.EulerFactors
