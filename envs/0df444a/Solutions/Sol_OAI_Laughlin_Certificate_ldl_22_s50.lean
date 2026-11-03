-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_22_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:32:58.658727+00:00
-- url     : https://prove2.me/submissions/0eff7ad3-e1ca-4524-a8c3-4304c96d9c70

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_22_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_22_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_11_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_13_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_15_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_17_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_19_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_21_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_9_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_22_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_22_3_1 : Y 22 3 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_3_s50

theorem source_error_22_5_1 : Y 22 5 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_5_s50

theorem source_error_22_5_3 : Y 22 5 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_5_s50

theorem source_error_22_7_1 : Y 22 7 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_7_s50

theorem source_error_22_7_3 : Y 22 7 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_7_s50

theorem source_error_22_7_5 : Y 22 7 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_7_s50

theorem source_error_22_9_1 : Y 22 9 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_9_s50

theorem source_error_22_9_3 : Y 22 9 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_9_s50

theorem source_error_22_9_5 : Y 22 9 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_9_s50

theorem source_error_22_9_7 : Y 22 9 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_7_9_s50

theorem source_error_22_11_1 : Y 22 11 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_11_s50

theorem source_error_22_11_3 : Y 22 11 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_11_s50

theorem source_error_22_11_5 : Y 22 11 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_11_s50

theorem source_error_22_11_7 : Y 22 11 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_7_11_s50

theorem source_error_22_11_9 : Y 22 11 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_9_11_s50

theorem source_error_22_13_1 : Y 22 13 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_13_s50

theorem source_error_22_13_3 : Y 22 13 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_13_s50

theorem source_error_22_13_5 : Y 22 13 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_13_s50

theorem source_error_22_13_7 : Y 22 13 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_7_13_s50

theorem source_error_22_13_9 : Y 22 13 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_9_13_s50

theorem source_error_22_13_11 : Y 22 13 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_11_13_s50

theorem source_error_22_15_1 : Y 22 15 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_15_s50

theorem source_error_22_15_3 : Y 22 15 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_15_s50

theorem source_error_22_15_5 : Y 22 15 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_15_s50

theorem source_error_22_15_7 : Y 22 15 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_7_15_s50

theorem source_error_22_15_9 : Y 22 15 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_9_15_s50

theorem source_error_22_15_11 : Y 22 15 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_11_15_s50

theorem source_error_22_15_13 : Y 22 15 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_13_15_s50

theorem source_error_22_17_1 : Y 22 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_17_s50

theorem source_error_22_17_3 : Y 22 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_17_s50

theorem source_error_22_17_5 : Y 22 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_17_s50

theorem source_error_22_17_7 : Y 22 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_7_17_s50

theorem source_error_22_17_9 : Y 22 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_9_17_s50

theorem source_error_22_17_11 : Y 22 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_11_17_s50

theorem source_error_22_17_13 : Y 22 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_13_17_s50

theorem source_error_22_17_15 : Y 22 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_15_17_s50

theorem source_error_22_19_1 : Y 22 19 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_19_s50

theorem source_error_22_19_3 : Y 22 19 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_19_s50

theorem source_error_22_19_5 : Y 22 19 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_19_s50

theorem source_error_22_19_7 : Y 22 19 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_7_19_s50

theorem source_error_22_19_9 : Y 22 19 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_9_19_s50

theorem source_error_22_19_11 : Y 22 19 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_11_19_s50

theorem source_error_22_19_13 : Y 22 19 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_13_19_s50

theorem source_error_22_19_15 : Y 22 19 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_15_19_s50

theorem source_error_22_19_17 : Y 22 19 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_17_19_s50

theorem source_error_22_21_1 : Y 22 21 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_1_21_s50

theorem source_error_22_21_3 : Y 22 21 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_3_21_s50

theorem source_error_22_21_5 : Y 22 21 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_5_21_s50

theorem source_error_22_21_7 : Y 22 21 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_7_21_s50

theorem source_error_22_21_9 : Y 22 21 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_9_21_s50

theorem source_error_22_21_11 : Y 22 21 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_11_21_s50

theorem source_error_22_21_13 : Y 22 21 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_13_21_s50

theorem source_error_22_21_15 : Y 22 21 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_15_21_s50

theorem source_error_22_21_17 : Y 22 21 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_17_21_s50

theorem source_error_22_21_19 : Y 22 21 19 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_22_19_21_s50

theorem error_22 : errorRational 22 = candidateY_22 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_22_1_1_s50
  · exact source_error_22_1_3_s50
  · exact source_error_22_1_5_s50
  · exact source_error_22_1_7_s50
  · exact source_error_22_1_9_s50
  · exact source_error_22_1_11_s50
  · exact source_error_22_1_13_s50
  · exact source_error_22_1_15_s50
  · exact source_error_22_1_17_s50
  · exact source_error_22_1_19_s50
  · exact source_error_22_1_21_s50
  · exact source_error_22_3_1
  · exact source_error_22_3_3_s50
  · exact source_error_22_3_5_s50
  · exact source_error_22_3_7_s50
  · exact source_error_22_3_9_s50
  · exact source_error_22_3_11_s50
  · exact source_error_22_3_13_s50
  · exact source_error_22_3_15_s50
  · exact source_error_22_3_17_s50
  · exact source_error_22_3_19_s50
  · exact source_error_22_3_21_s50
  · exact source_error_22_5_1
  · exact source_error_22_5_3
  · exact source_error_22_5_5_s50
  · exact source_error_22_5_7_s50
  · exact source_error_22_5_9_s50
  · exact source_error_22_5_11_s50
  · exact source_error_22_5_13_s50
  · exact source_error_22_5_15_s50
  · exact source_error_22_5_17_s50
  · exact source_error_22_5_19_s50
  · exact source_error_22_5_21_s50
  · exact source_error_22_7_1
  · exact source_error_22_7_3
  · exact source_error_22_7_5
  · exact source_error_22_7_7_s50
  · exact source_error_22_7_9_s50
  · exact source_error_22_7_11_s50
  · exact source_error_22_7_13_s50
  · exact source_error_22_7_15_s50
  · exact source_error_22_7_17_s50
  · exact source_error_22_7_19_s50
  · exact source_error_22_7_21_s50
  · exact source_error_22_9_1
  · exact source_error_22_9_3
  · exact source_error_22_9_5
  · exact source_error_22_9_7
  · exact source_error_22_9_9_s50
  · exact source_error_22_9_11_s50
  · exact source_error_22_9_13_s50
  · exact source_error_22_9_15_s50
  · exact source_error_22_9_17_s50
  · exact source_error_22_9_19_s50
  · exact source_error_22_9_21_s50
  · exact source_error_22_11_1
  · exact source_error_22_11_3
  · exact source_error_22_11_5
  · exact source_error_22_11_7
  · exact source_error_22_11_9
  · exact source_error_22_11_11_s50
  · exact source_error_22_11_13_s50
  · exact source_error_22_11_15_s50
  · exact source_error_22_11_17_s50
  · exact source_error_22_11_19_s50
  · exact source_error_22_11_21_s50
  · exact source_error_22_13_1
  · exact source_error_22_13_3
  · exact source_error_22_13_5
  · exact source_error_22_13_7
  · exact source_error_22_13_9
  · exact source_error_22_13_11
  · exact source_error_22_13_13_s50
  · exact source_error_22_13_15_s50
  · exact source_error_22_13_17_s50
  · exact source_error_22_13_19_s50
  · exact source_error_22_13_21_s50
  · exact source_error_22_15_1
  · exact source_error_22_15_3
  · exact source_error_22_15_5
  · exact source_error_22_15_7
  · exact source_error_22_15_9
  · exact source_error_22_15_11
  · exact source_error_22_15_13
  · exact source_error_22_15_15_s50
  · exact source_error_22_15_17_s50
  · exact source_error_22_15_19_s50
  · exact source_error_22_15_21_s50
  · exact source_error_22_17_1
  · exact source_error_22_17_3
  · exact source_error_22_17_5
  · exact source_error_22_17_7
  · exact source_error_22_17_9
  · exact source_error_22_17_11
  · exact source_error_22_17_13
  · exact source_error_22_17_15
  · exact source_error_22_17_17_s50
  · exact source_error_22_17_19_s50
  · exact source_error_22_17_21_s50
  · exact source_error_22_19_1
  · exact source_error_22_19_3
  · exact source_error_22_19_5
  · exact source_error_22_19_7
  · exact source_error_22_19_9
  · exact source_error_22_19_11
  · exact source_error_22_19_13
  · exact source_error_22_19_15
  · exact source_error_22_19_17
  · exact source_error_22_19_19_s50
  · exact source_error_22_19_21_s50
  · exact source_error_22_21_1
  · exact source_error_22_21_3
  · exact source_error_22_21_5
  · exact source_error_22_21_7
  · exact source_error_22_21_9
  · exact source_error_22_21_11
  · exact source_error_22_21_13
  · exact source_error_22_21_15
  · exact source_error_22_21_17
  · exact source_error_22_21_19
  · exact source_error_22_21_21_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_22_s50_oai : compressedRational 22 =
    lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose := by
  rw [compressedRational_eq_compute, error_22, gram_22_s50]
  exact candidateLDL_22_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_22_s50_oai := @OAI.Laughlin.Certificate.ldl_22_s50_oai
