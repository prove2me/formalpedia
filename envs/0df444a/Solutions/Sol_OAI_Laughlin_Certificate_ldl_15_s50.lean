-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_15_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:26:56.572309+00:00
-- url     : https://prove2.me/submissions/5d4e67a2-faa6-47ec-b24c-3ef6d068a5cb

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_15_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_15_3_1 : Y 15 3 1 = (527769145158896263581537579/2097152000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_3_s50

theorem source_error_15_5_1 : Y 15 5 1 = (-364633884256427977153375413/1677721600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_5_s50

theorem source_error_15_5_3 : Y 15 5 3 = (10380910649344519579874271/838860800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_5_s50

theorem source_error_15_7_1 : Y 15 7 1 = (70800295830292526868599229/838860800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_7_s50

theorem source_error_15_7_3 : Y 15 7 3 = (2399450471501791440121389/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_7_s50

theorem source_error_15_7_5 : Y 15 7 5 = (-1550173356554793074510931/838860800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_7_s50

theorem source_error_15_9_1 : Y 15 9 1 = (-213215905018995130639958571/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_9_s50

theorem source_error_15_9_3 : Y 15 9 3 = (7831247768240800098462597/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_9_s50

theorem source_error_15_9_5 : Y 15 9 5 = (-251612565167710626302493/209715200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_9_s50

theorem source_error_15_9_7 : Y 15 9 7 = (483384920806779568744041/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_9_s50

theorem source_error_15_11_1 : Y 15 11 1 = (-236988935373506936612565573/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_11_s50

theorem source_error_15_11_3 : Y 15 11 3 = (260365051976410952573409/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_11_s50

theorem source_error_15_11_5 : Y 15 11 5 = (412467042517374252900789/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_11_s50

theorem source_error_15_11_7 : Y 15 11 7 = (-2196385127442123145785873/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_11_s50

theorem source_error_15_11_9 : Y 15 11 9 = (144198476217622441333917/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_9_11_s50

theorem source_error_15_13_1 : Y 15 13 1 = (374746885492881333249210393/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_13_s50

theorem source_error_15_13_3 : Y 15 13 3 = (15417580069242120546303813/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_13_s50

theorem source_error_15_13_5 : Y 15 13 5 = (-3917597116231063282740723/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_13_s50

theorem source_error_15_13_7 : Y 15 13 7 = (-3020058706667129324414217/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_13_s50

theorem source_error_15_13_9 : Y 15 13 9 = (-270537545003843608530039/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_9_13_s50

theorem source_error_15_13_11 : Y 15 13 11 = (-1188419411670004290171681/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_11_13_s50

theorem source_error_15_15_1 : Y 15 15 1 = (-1454272995490648196091417189/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_15_s50

theorem source_error_15_15_3 : Y 15 15 3 = (-19651317795670208550803901/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_15_s50

theorem source_error_15_15_5 : Y 15 15 5 = (6737890215993101774728119/10485760000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_15_s50

theorem source_error_15_15_7 : Y 15 15 7 = (6630571266894369608354541/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_15_s50

theorem source_error_15_15_9 : Y 15 15 9 = (488416974255188057862783/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_9_15_s50

theorem source_error_15_15_11 : Y 15 15 11 = (-946932022961651320973379/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_11_15_s50

theorem source_error_15_15_13 : Y 15 15 13 = (6044229669744752465993013/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_13_15_s50

theorem error_15 : errorRational 15 = candidateY_15 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_15_1_1_s50
  · exact source_error_15_1_3_s50
  · exact source_error_15_1_5_s50
  · exact source_error_15_1_7_s50
  · exact source_error_15_1_9_s50
  · exact source_error_15_1_11_s50
  · exact source_error_15_1_13_s50
  · exact source_error_15_1_15_s50
  · exact source_error_15_3_1
  · exact source_error_15_3_3_s50
  · exact source_error_15_3_5_s50
  · exact source_error_15_3_7_s50
  · exact source_error_15_3_9_s50
  · exact source_error_15_3_11_s50
  · exact source_error_15_3_13_s50
  · exact source_error_15_3_15_s50
  · exact source_error_15_5_1
  · exact source_error_15_5_3
  · exact source_error_15_5_5_s50
  · exact source_error_15_5_7_s50
  · exact source_error_15_5_9_s50
  · exact source_error_15_5_11_s50
  · exact source_error_15_5_13_s50
  · exact source_error_15_5_15_s50
  · exact source_error_15_7_1
  · exact source_error_15_7_3
  · exact source_error_15_7_5
  · exact source_error_15_7_7_s50
  · exact source_error_15_7_9_s50
  · exact source_error_15_7_11_s50
  · exact source_error_15_7_13_s50
  · exact source_error_15_7_15_s50
  · exact source_error_15_9_1
  · exact source_error_15_9_3
  · exact source_error_15_9_5
  · exact source_error_15_9_7
  · exact source_error_15_9_9_s50
  · exact source_error_15_9_11_s50
  · exact source_error_15_9_13_s50
  · exact source_error_15_9_15_s50
  · exact source_error_15_11_1
  · exact source_error_15_11_3
  · exact source_error_15_11_5
  · exact source_error_15_11_7
  · exact source_error_15_11_9
  · exact source_error_15_11_11_s50
  · exact source_error_15_11_13_s50
  · exact source_error_15_11_15_s50
  · exact source_error_15_13_1
  · exact source_error_15_13_3
  · exact source_error_15_13_5
  · exact source_error_15_13_7
  · exact source_error_15_13_9
  · exact source_error_15_13_11
  · exact source_error_15_13_13_s50
  · exact source_error_15_13_15_s50
  · exact source_error_15_15_1
  · exact source_error_15_15_3
  · exact source_error_15_15_5
  · exact source_error_15_15_7
  · exact source_error_15_15_9
  · exact source_error_15_15_11
  · exact source_error_15_15_13
  · exact source_error_15_15_15_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_15_s50_oai : compressedRational 15 =
    lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose := by
  rw [compressedRational_eq_compute, error_15, gram_15_s50]
  exact candidateLDL_15_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_15_s50_oai := @OAI.Laughlin.Certificate.ldl_15_s50_oai
