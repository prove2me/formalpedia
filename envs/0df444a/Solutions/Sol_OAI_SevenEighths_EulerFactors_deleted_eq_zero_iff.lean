-- Prove2me | solution 1 for OAI.SevenEighths.EulerFactors.deleted_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:13:54.229055+00:00
-- url     : https://prove2.me/submissions/9a7306e0-572f-42e6-b899-1fb8fb9cc0b7

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_EulerFactors
import Theorems.Thm_OAI_SevenEighths_EulerFactors_deletedProduct_ne_zero

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.EulerFactors
noncomputable section
namespace OAI.SevenEighths.EulerFactors
theorem _root_.solution {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {L Ldeleted : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hidentity : Ldeleted s = deletedProduct S N a s * L s) :
    Ldeleted s = 0 ↔ L s = 0 := by
  rw [hidentity, mul_eq_zero]
  exact or_iff_right (deletedProduct_ne_zero S N a hN ha hs)
end OAI.SevenEighths.EulerFactors
