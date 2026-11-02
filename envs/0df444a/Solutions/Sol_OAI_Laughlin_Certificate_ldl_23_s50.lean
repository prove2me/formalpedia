-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_23_s50
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:34:33.842872+00:00
-- url     : https://prove2.me/submissions/8b4f5372-5386-41ea-8111-a7b9816aa317
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_23_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_9_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_NumericBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem compressedRational_eq_compute (D : ℕ) :
    compressedRational D = MatrixCompute.compressed D (errorRational D) (gramRational D) := by
  rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_swap (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1 + e.2.1) (hf : t ≤ f.1 + f.2.1) :
    yEntry D r s t e f = yEntry D s r t f e := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at he hf
  have hT : q+l+(p+j-t) = p+j+(q+l-t) := by omega
  simp only [yEntry, hT, Nat.add_comm s r]
  split_ifs <;> ring_nf

private theorem sum_add {Element : Type*} (xs : List Element) (f g : Element → ℚ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_swap {Element : Type*} (xs ys : List Element)
    (f : Element → Element → ℚ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, sum_add]

theorem yRow_swap (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (h : ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1) :
    yRow D r s row = yRow D s r row := by
  unfold yRow
  rw [sum_swap]
  congr 1
  apply List.map_congr_left
  intro f hf
  congr 1
  apply List.map_congr_left
  intro e he
  exact yEntry_swap D r s row.1 e f (h e he) (h f hf)

theorem rows_valid : ∀ row ∈ rows, ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1 := by
  decide +kernel

theorem Y_symm (D r s : ℕ) : Y D r s = Y D s r := by
  unfold Y
  congr 3
  apply List.map_congr_left
  intro row hr
  exact yRow_swap D r s row (rows_valid row hr)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_23_3_1 : Y 23 3 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_3_s50

theorem source_error_23_5_1 : Y 23 5 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_5_s50

theorem source_error_23_5_3 : Y 23 5 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_5_s50

theorem source_error_23_7_1 : Y 23 7 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_7_s50

theorem source_error_23_7_3 : Y 23 7 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_7_s50

theorem source_error_23_7_5 : Y 23 7 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_7_s50

theorem source_error_23_9_1 : Y 23 9 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_9_s50

theorem source_error_23_9_3 : Y 23 9 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_9_s50

theorem source_error_23_9_5 : Y 23 9 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_9_s50

theorem source_error_23_9_7 : Y 23 9 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_9_s50

theorem source_error_23_11_1 : Y 23 11 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_11_s50

theorem source_error_23_11_3 : Y 23 11 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_11_s50

theorem source_error_23_11_5 : Y 23 11 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_11_s50

theorem source_error_23_11_7 : Y 23 11 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_11_s50

theorem source_error_23_11_9 : Y 23 11 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_9_11_s50

theorem source_error_23_13_1 : Y 23 13 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_13_s50

theorem source_error_23_13_3 : Y 23 13 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_13_s50

theorem source_error_23_13_5 : Y 23 13 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_13_s50

theorem source_error_23_13_7 : Y 23 13 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_13_s50

theorem source_error_23_13_9 : Y 23 13 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_9_13_s50

theorem source_error_23_13_11 : Y 23 13 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_11_13_s50

theorem source_error_23_15_1 : Y 23 15 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_15_s50

theorem source_error_23_15_3 : Y 23 15 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_15_s50

theorem source_error_23_15_5 : Y 23 15 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_15_s50

theorem source_error_23_15_7 : Y 23 15 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_15_s50

theorem source_error_23_15_9 : Y 23 15 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_9_15_s50

theorem source_error_23_15_11 : Y 23 15 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_11_15_s50

theorem source_error_23_15_13 : Y 23 15 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_13_15_s50

theorem source_error_23_17_1 : Y 23 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_17_s50

theorem source_error_23_17_3 : Y 23 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_17_s50

theorem source_error_23_17_5 : Y 23 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_17_s50

theorem source_error_23_17_7 : Y 23 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_17_s50

theorem source_error_23_17_9 : Y 23 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_9_17_s50

theorem source_error_23_17_11 : Y 23 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_11_17_s50

theorem source_error_23_17_13 : Y 23 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_13_17_s50

theorem source_error_23_17_15 : Y 23 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_15_17_s50

theorem source_error_23_19_1 : Y 23 19 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_19_s50

theorem source_error_23_19_3 : Y 23 19 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_19_s50

theorem source_error_23_19_5 : Y 23 19 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_19_s50

theorem source_error_23_19_7 : Y 23 19 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_19_s50

theorem source_error_23_19_9 : Y 23 19 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_9_19_s50

theorem source_error_23_19_11 : Y 23 19 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_11_19_s50

theorem source_error_23_19_13 : Y 23 19 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_13_19_s50

theorem source_error_23_19_15 : Y 23 19 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_15_19_s50

theorem source_error_23_19_17 : Y 23 19 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_17_19_s50

theorem source_error_23_21_1 : Y 23 21 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_21_s50

theorem source_error_23_21_3 : Y 23 21 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_21_s50

theorem source_error_23_21_5 : Y 23 21 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_21_s50

theorem source_error_23_21_7 : Y 23 21 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_21_s50

theorem source_error_23_21_9 : Y 23 21 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_9_21_s50

theorem source_error_23_21_11 : Y 23 21 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_11_21_s50

theorem source_error_23_21_13 : Y 23 21 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_13_21_s50

theorem source_error_23_21_15 : Y 23 21 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_15_21_s50

theorem source_error_23_21_17 : Y 23 21 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_17_21_s50

theorem source_error_23_21_19 : Y 23 21 19 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_19_21_s50

theorem source_error_23_23_1 : Y 23 23 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_1_23_s50

theorem source_error_23_23_3 : Y 23 23 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_3_23_s50

theorem source_error_23_23_5 : Y 23 23 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_5_23_s50

theorem source_error_23_23_7 : Y 23 23 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_7_23_s50

theorem source_error_23_23_9 : Y 23 23 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_9_23_s50

theorem source_error_23_23_11 : Y 23 23 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_11_23_s50

theorem source_error_23_23_13 : Y 23 23 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_13_23_s50

theorem source_error_23_23_15 : Y 23 23 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_15_23_s50

theorem source_error_23_23_17 : Y 23 23 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_17_23_s50

theorem source_error_23_23_19 : Y 23 23 19 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_19_23_s50

theorem source_error_23_23_21 : Y 23 23 21 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_23_21_23_s50

theorem error_23 : errorRational 23 = candidateY_23 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_23_1_1_s50
  · exact source_error_23_1_3_s50
  · exact source_error_23_1_5_s50
  · exact source_error_23_1_7_s50
  · exact source_error_23_1_9_s50
  · exact source_error_23_1_11_s50
  · exact source_error_23_1_13_s50
  · exact source_error_23_1_15_s50
  · exact source_error_23_1_17_s50
  · exact source_error_23_1_19_s50
  · exact source_error_23_1_21_s50
  · exact source_error_23_1_23_s50
  · exact source_error_23_3_1
  · exact source_error_23_3_3_s50
  · exact source_error_23_3_5_s50
  · exact source_error_23_3_7_s50
  · exact source_error_23_3_9_s50
  · exact source_error_23_3_11_s50
  · exact source_error_23_3_13_s50
  · exact source_error_23_3_15_s50
  · exact source_error_23_3_17_s50
  · exact source_error_23_3_19_s50
  · exact source_error_23_3_21_s50
  · exact source_error_23_3_23_s50
  · exact source_error_23_5_1
  · exact source_error_23_5_3
  · exact source_error_23_5_5_s50
  · exact source_error_23_5_7_s50
  · exact source_error_23_5_9_s50
  · exact source_error_23_5_11_s50
  · exact source_error_23_5_13_s50
  · exact source_error_23_5_15_s50
  · exact source_error_23_5_17_s50
  · exact source_error_23_5_19_s50
  · exact source_error_23_5_21_s50
  · exact source_error_23_5_23_s50
  · exact source_error_23_7_1
  · exact source_error_23_7_3
  · exact source_error_23_7_5
  · exact source_error_23_7_7_s50
  · exact source_error_23_7_9_s50
  · exact source_error_23_7_11_s50
  · exact source_error_23_7_13_s50
  · exact source_error_23_7_15_s50
  · exact source_error_23_7_17_s50
  · exact source_error_23_7_19_s50
  · exact source_error_23_7_21_s50
  · exact source_error_23_7_23_s50
  · exact source_error_23_9_1
  · exact source_error_23_9_3
  · exact source_error_23_9_5
  · exact source_error_23_9_7
  · exact source_error_23_9_9_s50
  · exact source_error_23_9_11_s50
  · exact source_error_23_9_13_s50
  · exact source_error_23_9_15_s50
  · exact source_error_23_9_17_s50
  · exact source_error_23_9_19_s50
  · exact source_error_23_9_21_s50
  · exact source_error_23_9_23_s50
  · exact source_error_23_11_1
  · exact source_error_23_11_3
  · exact source_error_23_11_5
  · exact source_error_23_11_7
  · exact source_error_23_11_9
  · exact source_error_23_11_11_s50
  · exact source_error_23_11_13_s50
  · exact source_error_23_11_15_s50
  · exact source_error_23_11_17_s50
  · exact source_error_23_11_19_s50
  · exact source_error_23_11_21_s50
  · exact source_error_23_11_23_s50
  · exact source_error_23_13_1
  · exact source_error_23_13_3
  · exact source_error_23_13_5
  · exact source_error_23_13_7
  · exact source_error_23_13_9
  · exact source_error_23_13_11
  · exact source_error_23_13_13_s50
  · exact source_error_23_13_15_s50
  · exact source_error_23_13_17_s50
  · exact source_error_23_13_19_s50
  · exact source_error_23_13_21_s50
  · exact source_error_23_13_23_s50
  · exact source_error_23_15_1
  · exact source_error_23_15_3
  · exact source_error_23_15_5
  · exact source_error_23_15_7
  · exact source_error_23_15_9
  · exact source_error_23_15_11
  · exact source_error_23_15_13
  · exact source_error_23_15_15_s50
  · exact source_error_23_15_17_s50
  · exact source_error_23_15_19_s50
  · exact source_error_23_15_21_s50
  · exact source_error_23_15_23_s50
  · exact source_error_23_17_1
  · exact source_error_23_17_3
  · exact source_error_23_17_5
  · exact source_error_23_17_7
  · exact source_error_23_17_9
  · exact source_error_23_17_11
  · exact source_error_23_17_13
  · exact source_error_23_17_15
  · exact source_error_23_17_17_s50
  · exact source_error_23_17_19_s50
  · exact source_error_23_17_21_s50
  · exact source_error_23_17_23_s50
  · exact source_error_23_19_1
  · exact source_error_23_19_3
  · exact source_error_23_19_5
  · exact source_error_23_19_7
  · exact source_error_23_19_9
  · exact source_error_23_19_11
  · exact source_error_23_19_13
  · exact source_error_23_19_15
  · exact source_error_23_19_17
  · exact source_error_23_19_19_s50
  · exact source_error_23_19_21_s50
  · exact source_error_23_19_23_s50
  · exact source_error_23_21_1
  · exact source_error_23_21_3
  · exact source_error_23_21_5
  · exact source_error_23_21_7
  · exact source_error_23_21_9
  · exact source_error_23_21_11
  · exact source_error_23_21_13
  · exact source_error_23_21_15
  · exact source_error_23_21_17
  · exact source_error_23_21_19
  · exact source_error_23_21_21_s50
  · exact source_error_23_21_23_s50
  · exact source_error_23_23_1
  · exact source_error_23_23_3
  · exact source_error_23_23_5
  · exact source_error_23_23_7
  · exact source_error_23_23_9
  · exact source_error_23_23_11
  · exact source_error_23_23_13
  · exact source_error_23_23_15
  · exact source_error_23_23_17
  · exact source_error_23_23_19
  · exact source_error_23_23_21
  · exact source_error_23_23_23_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_23_s50_oai : compressedRational 23 =
    lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose := by
  rw [compressedRational_eq_compute, error_23, gram_23_s50]
  exact candidateLDL_23_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_23_s50_oai := @OAI.Laughlin.Certificate.ldl_23_s50_oai
