-- Prove2me | solution 1 for N4Code.dRow_replace_27_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:24.194363+00:00
-- url     : https://prove2.me/submissions/99305bcc-fcd6-4594-be3b-91681e2efed0

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow_eq_indicator_sum


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (j : Fin 4) (hj : j ≠ 2) (y : Word n) (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) j y = dRow C j y := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu1 : u = t₁
  · by_cases hu2 : u = t₂
    · exfalso
      exact htne (hu1.symm.trans hu2)
    · simp [replaceColumn, hu1, h1]
      have ht' : ¬ t₁ = t₂ := fun h => hu2 (hu1.trans h)
      simp [if_neg ht']
      have hb : colBit j col3 = colBit j col1 := by
        fin_cases j <;> simp [colBit, col1, col3] at hj ⊢
      rw [hb]
  · by_cases hu2 : u = t₂
    · simp [replaceColumn, hu2, h7]
      have hb : colBit j col5 = colBit j col7 := by
        fin_cases j <;> simp [colBit, col7, col5] at hj ⊢
      simp [hb]
    · simp [replaceColumn, hu1, hu2]
end N4Code
