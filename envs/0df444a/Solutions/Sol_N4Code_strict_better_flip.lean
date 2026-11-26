-- Prove2me | solution 1 for N4Code.strict_better_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:18.895793+00:00
-- url     : https://prove2.me/submissions/70b44e86-3491-4deb-8aec-343ddfef8677

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_rowPermute_refl
import Theorems.Thm_N4Code_lambda_equiv


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s : Column)
    (h : UniversalStrictBetter (replaceColumn C t s) C) :
    UniversalStrictBetter (replaceColumn C t (flipCol s)) C := by
  intro ε hε0 hε1
  have hEq : Equivalent (replaceColumn C t s) (replaceColumn C t (flipCol s)) := by
    refine ⟨Equiv.refl (Fin 4), Equiv.refl (Fin n), fun u => decide (u = t), ?_⟩
    intro u
    by_cases hu : u = t
    · subst u
      simp [replaceColumn, rowPermute_refl]
    · simp [replaceColumn, hu, rowPermute_refl]
  have hl : lambda (replaceColumn C t (flipCol s)) ε = lambda (replaceColumn C t s) ε :=
    lambda_equiv (replaceColumn C t s) (replaceColumn C t (flipCol s)) hEq ε
  rw [hl]
  exact h ε hε0 hε1
end N4Code
