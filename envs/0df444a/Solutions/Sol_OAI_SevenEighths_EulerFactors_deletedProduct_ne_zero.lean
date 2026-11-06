-- Prove2me | solution 1 for OAI.SevenEighths.EulerFactors.deletedProduct_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:52:59.811476+00:00
-- url     : https://prove2.me/submissions/6634de95-6c56-48d7-ad59-07fe6402ab1b

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_EulerFactors
import Theorems.Thm_OAI_SevenEighths_EulerFactors_factor_ne_zero

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.EulerFactors
noncomputable section
namespace OAI.SevenEighths.EulerFactors
theorem _root_.solution {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs
end OAI.SevenEighths.EulerFactors
