-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_13_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:25:20.363811+00:00
-- url     : https://prove2.me/submissions/0c0dee8a-784b-43c4-8653-19d5f776764a

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_13_3_1 : Y 13 3 1 = (7563908306608840424871171/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_3_s50

theorem source_error_13_5_1 : Y 13 5 1 = (-66091999624888726298111247/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_5_s50

theorem source_error_13_5_3 : Y 13 5 3 = (126715690823288866730217/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_5_s50

theorem source_error_13_7_1 : Y 13 7 1 = (2728798823338271240310567/1677721600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_7_s50

theorem source_error_13_7_3 : Y 13 7 3 = (-500594098074230841463629/2097152000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_7_s50

theorem source_error_13_7_5 : Y 13 7 5 = (701982483744393187744923/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_7_s50

theorem source_error_13_9_1 : Y 13 9 1 = (-13501297339814524797227781/10485760000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_9_s50

theorem source_error_13_9_3 : Y 13 9 3 = (-1215155073315811787592453/2621440000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_9_s50

theorem source_error_13_9_5 : Y 13 9 5 = (672840394965225922256721/2097152000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_9_s50

theorem source_error_13_9_7 : Y 13 9 7 = (-175665130303631642663517/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_7_9_s50

theorem source_error_13_11_1 : Y 13 11 1 = (12432022452888993488134359/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_11_s50

theorem source_error_13_11_3 : Y 13 11 3 = (-47337050492347165740927/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_11_s50

theorem source_error_13_11_5 : Y 13 11 5 = (2506297034373528441573/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_11_s50

theorem source_error_13_11_7 : Y 13 11 7 = (420722950805223871087107/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_7_11_s50

theorem source_error_13_11_9 : Y 13 11 9 = (1437479079722043725179197/655360000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_9_11_s50

theorem source_error_13_13_1 : Y 13 13 1 = (-165874530574631465579316753/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_13_s50

theorem source_error_13_13_3 : Y 13 13 3 = (-394753123867351949086959/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_13_s50

theorem source_error_13_13_5 : Y 13 13 5 = (5534718096701578046307903/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_13_s50

theorem source_error_13_13_7 : Y 13 13 7 = (-2485443250416390286101651/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_7_13_s50

theorem source_error_13_13_9 : Y 13 13 9 = (-2022830025440980274156781/655360000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_9_13_s50

theorem source_error_13_13_11 : Y 13 13 11 = (252554056596275363975331/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_11_13_s50

theorem error_13 : errorRational 13 = candidateY_13 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_13_1_1_s50
  · exact source_error_13_1_3_s50
  · exact source_error_13_1_5_s50
  · exact source_error_13_1_7_s50
  · exact source_error_13_1_9_s50
  · exact source_error_13_1_11_s50
  · exact source_error_13_1_13_s50
  · exact source_error_13_3_1
  · exact source_error_13_3_3_s50
  · exact source_error_13_3_5_s50
  · exact source_error_13_3_7_s50
  · exact source_error_13_3_9_s50
  · exact source_error_13_3_11_s50
  · exact source_error_13_3_13_s50
  · exact source_error_13_5_1
  · exact source_error_13_5_3
  · exact source_error_13_5_5_s50
  · exact source_error_13_5_7_s50
  · exact source_error_13_5_9_s50
  · exact source_error_13_5_11_s50
  · exact source_error_13_5_13_s50
  · exact source_error_13_7_1
  · exact source_error_13_7_3
  · exact source_error_13_7_5
  · exact source_error_13_7_7_s50
  · exact source_error_13_7_9_s50
  · exact source_error_13_7_11_s50
  · exact source_error_13_7_13_s50
  · exact source_error_13_9_1
  · exact source_error_13_9_3
  · exact source_error_13_9_5
  · exact source_error_13_9_7
  · exact source_error_13_9_9_s50
  · exact source_error_13_9_11_s50
  · exact source_error_13_9_13_s50
  · exact source_error_13_11_1
  · exact source_error_13_11_3
  · exact source_error_13_11_5
  · exact source_error_13_11_7
  · exact source_error_13_11_9
  · exact source_error_13_11_11_s50
  · exact source_error_13_11_13_s50
  · exact source_error_13_13_1
  · exact source_error_13_13_3
  · exact source_error_13_13_5
  · exact source_error_13_13_7
  · exact source_error_13_13_9
  · exact source_error_13_13_11
  · exact source_error_13_13_13_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_13_s50_oai : compressedRational 13 =
    lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose := by
  rw [compressedRational_eq_compute, error_13, gram_13_s50]
  exact candidateLDL_13_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_13_s50_oai := @OAI.Laughlin.Certificate.ldl_13_s50_oai
