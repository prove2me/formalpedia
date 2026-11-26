-- Prove2me | solution 1 for N4Code.dRow_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:53.364402+00:00
-- url     : https://prove2.me/submissions/9ba81b92-61d9-4008-9301-b9f64c57ccde

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_dRow_eq_indicator_sum

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) {ρ : Equiv (Fin 4) (Fin 4)}
    {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (h : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    (j : Fin 4) (y : Word n) :
    dRow C' j y = dRow C (ρ j) (wordTransform p f y) := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  calc
    (∑ t : Fin n, if colBit j (C' t) ≠ y t then 1 else 0)
        = ∑ t : Fin n, if colBit j (C' (p t)) ≠ y (p t) then 1 else 0 := by
          symm
          apply Finset.sum_bij (fun t _ => p t)
          · intro t _; simp
          · intro a _ b _ hab
            exact p.injective hab
          · intro b _
            exact ⟨p.symm b, by simp, by simp⟩
          · intro t _; rfl
    _ = ∑ t : Fin n, if colBit (ρ j) (C t) ≠ wordTransform p f y t then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro t _
          have hcol : colBit j (C' (p t)) =
              if f t then !(colBit (ρ j) (C t)) else colBit (ρ j) (C t) := by
            rw [h t]
            by_cases hf : f t = true <;> simp [rowPermute, flipCol, colBit, hf]
          by_cases hf : f t <;> simp [wordTransform, hf, hcol]
end N4Code
