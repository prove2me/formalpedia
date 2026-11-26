-- Prove2me | solution 1 for N4Code.allEvenWeights_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:41.275781+00:00
-- url     : https://prove2.me/submissions/1d0cfd6a-b8a8-4f7e-a849-a427e5057c78

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_colWeight_rowPermute
import Theorems.Thm_N4Code_colWeight_flip
import Theorems.Thm_N4Code_colWeight_le_4
import Theorems.Thm_N4Code_even_weight_iff

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (h : Equivalent C C') :
    allEvenWeights C ↔ allEvenWeights C' := by
  rcases h with ⟨ρ, p, f, h⟩
  have hrel : ∀ t : Fin n, colWeight (C' (p t)) = colWeight (C t) ∨
      colWeight (C' (p t)) = 4 - colWeight (C t) := by
    intro t
    rw [h t]
    cases hf : f t <;> simp [colWeight_rowPermute, colWeight_flip]
  constructor
  · intro hc t
    have ht' : C' t = C' (p (p.symm t)) := by simp
    rw [ht']
    exact (even_weight_iff (hrel (p.symm t)) (colWeight_le_4 _) (colWeight_le_4 _)).mpr
      (hc (p.symm t))
  · intro hc t
    exact (even_weight_iff (hrel t) (colWeight_le_4 _) (colWeight_le_4 _)).mp (hc (p t))
end N4Code
