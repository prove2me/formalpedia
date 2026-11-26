-- Prove2me | solution 1 for N4Code.twobitCount_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:21.958865+00:00
-- url     : https://prove2.me/submissions/e553f15f-4497-4979-a32b-119f0fd50d27

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colWeight_flip
import Theorems.Thm_N4Code_colWeight_le_4
import Theorems.Thm_N4Code_colWeight_rowPermute


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} {C C' : Code n} (h : Equivalent C C') :
    twobitCount C = twobitCount C' := by
  rcases h with ⟨ρ, p, f, hh⟩
  unfold twobitCount
  have hiff : ∀ t : Fin n, colWeight (C' (p t)) = 2 ↔ colWeight (C t) = 2 := by
    intro t
    have hrel : colWeight (C' (p t)) = colWeight (C t) ∨
        colWeight (C' (p t)) = 4 - colWeight (C t) := by
      rw [hh t]
      cases hf : f t <;> simp [colWeight_rowPermute, colWeight_flip]
    constructor
    · intro hw
      rcases hrel with h | h
      · omega
      · have hle : colWeight (C t) ≤ 4 := colWeight_le_4 (C t)
        omega
    · intro hw
      rcases hrel with h | h
      · omega
      · have hle : colWeight (C t) ≤ 4 := colWeight_le_4 (C t)
        omega
  apply Finset.card_bij (fun t _ => p t)
  · intro t ht
    exact Finset.mem_filter.mpr ⟨by simp, (hiff t).mpr (Finset.mem_filter.mp ht).2⟩
  · intro a _ b _ hab
    exact p.injective hab
  · intro b hb
    refine ⟨p.symm b, ?_, by simp⟩
    have hb' : colWeight (C' (p (p.symm b))) = 2 := by simpa using (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨by simp, (hiff (p.symm b)).mp hb'⟩
end N4Code
