-- Prove2me | solution 1 for N4Code.Columns07_le7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:40.19705+00:00
-- url     : https://prove2.me/submissions/a445f09d-f622-457e-bab2-dca84c50b896

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : Columns07 C) (t : Fin n) : colVal (C t) ≤ 7 := by
  let z : Fin 4 := ⟨0, by decide⟩
  have hb : (C t) z = false := h t
  let hf : Fin 4 → ℕ := fun j => if C t j then 2 ^ (3 - j.val) else 0
  have hsplit := sum_split_at hf z
  calc
    colVal (C t) = (∑ j : Fin 4, hf j) := by rfl
    _ = (∑ j ∈ (Finset.univ.erase z), hf j) + hf z := hsplit
    _ = (∑ j ∈ (Finset.univ.erase z), hf j) + 0 := by
          simp [hf, hb]
    _ ≤ (∑ j ∈ (Finset.univ.erase z), 2 ^ (3 - j.val)) + 0 := by
          have hle : (∑ j ∈ (Finset.univ.erase z), hf j) ≤
              ∑ j ∈ (Finset.univ.erase z), 2 ^ (3 - j.val) := by
            apply Finset.sum_le_sum
            intro j _
            by_cases hc : C t j <;> simp [hf, hc]
          omega
    _ = 7 := by
          have hsum : (∑ j ∈ (Finset.univ.erase z), 2 ^ (3 - j.val)) = 7 := by
            have huniv : (Finset.univ.erase z : Finset (Fin 4)) =
                ({⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩} : Finset (Fin 4)) := by
              ext j
              fin_cases j <;> simp [z]
            rw [huniv]
            simp
          rw [hsum]
end N4Code
