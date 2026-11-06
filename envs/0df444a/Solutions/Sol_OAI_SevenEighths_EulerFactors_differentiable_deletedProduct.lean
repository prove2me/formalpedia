-- Prove2me | solution 1 for OAI.SevenEighths.EulerFactors.differentiable_deletedProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:13:50.807714+00:00
-- url     : https://prove2.me/submissions/ca8fa2c9-60e2-477a-9998-8492b2c98a4a

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_EulerFactors
import Theorems.Thm_OAI_SevenEighths_EulerFactors_differentiable_factor

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.EulerFactors
noncomputable section
namespace OAI.SevenEighths.EulerFactors
theorem _root_.solution {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)
end OAI.SevenEighths.EulerFactors
