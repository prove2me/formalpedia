-- Prove2me | solution 1 for N4Code.lambda_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:22.768768+00:00
-- url     : https://prove2.me/submissions/f31dff2f-94e9-4716-8763-bc0916146cc7

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_wordTransform_inv_left
import Theorems.Thm_N4Code_wordTransform_bijective
import Theorems.Thm_N4Code_dCode_equiv

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (h : Equivalent C C') (ε : ℝ) :
    lambda C' ε = lambda C ε := by
  rcases h with ⟨ρ, p, f, h⟩
  have hd : ∀ y : Word n, dCode C' y = dCode C (wordTransform p f y) := dCode_equiv C C' h
  unfold lambda
  congr 1
  calc
    (∑ y : Word n, (1 - ε) ^ (n - dCode C' y) * ε ^ (dCode C' y))
        = ∑ y : Word n, (1 - ε) ^ (n - dCode C (wordTransform p f y)) * ε ^ (dCode C (wordTransform p f y)) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hd y]
    _ = ∑ y : Word n, (1 - ε) ^ (n - dCode C y) * ε ^ (dCode C y) := by
          apply Finset.sum_bij (fun y _ => wordTransform p f y)
          · intro y _; simp
          · intro a _ b _ hab
            exact (wordTransform_bijective p f).1 hab
          · intro b _
            exact ⟨wordTransformInv p f b, by simp, wordTransform_inv_left p f b⟩
          · intro y _; rfl
end N4Code
