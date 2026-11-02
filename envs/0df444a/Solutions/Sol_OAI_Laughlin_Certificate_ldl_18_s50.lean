-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_18_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:28:57.710705+00:00
-- url     : https://prove2.me/submissions/f6c5027e-053a-49bd-bbe4-40e7ece83bfb

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_18_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_18_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_18_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_18_3_1 : Y 18 3 1 = (43700029260178412251303173/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_3_s50

theorem source_error_18_5_1 : Y 18 5 1 = (-157097886646298732847063351/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_5_s50

theorem source_error_18_5_3 : Y 18 5 3 = (5636036629375968042063837/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_5_s50

theorem source_error_18_7_1 : Y 18 7 1 = (45795850251189055946275347/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_7_s50

theorem source_error_18_7_3 : Y 18 7 3 = (-2298714004872189626128407/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_7_s50

theorem source_error_18_7_5 : Y 18 7 5 = (3236875371562490528333463/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_7_s50

theorem source_error_18_9_1 : Y 18 9 1 = (-15768543277252499592049191/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_9_s50

theorem source_error_18_9_3 : Y 18 9 3 = (297813059860269307535181/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_9_s50

theorem source_error_18_9_5 : Y 18 9 5 = (109159200441997398693/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_9_s50

theorem source_error_18_9_7 : Y 18 9 7 = (76480320836604209603463/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_9_s50

theorem source_error_18_11_1 : Y 18 11 1 = (15774590706413201698776741/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_11_s50

theorem source_error_18_11_3 : Y 18 11 3 = (-427966983073658698687017/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_11_s50

theorem source_error_18_11_5 : Y 18 11 5 = (-76974792598120601955771/524288000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_11_s50

theorem source_error_18_11_7 : Y 18 11 7 = (34507713700153945513647/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_11_s50

theorem source_error_18_11_9 : Y 18 11 9 = (50562764756881342854273/327680000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_11_s50

theorem source_error_18_13_1 : Y 18 13 1 = (-111481601475376052708801013/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_13_s50

theorem source_error_18_13_3 : Y 18 13 3 = (460639052423449997118021/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_13_s50

theorem source_error_18_13_5 : Y 18 13 5 = (525900691396984091231043/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_13_s50

theorem source_error_18_13_7 : Y 18 13 7 = (-126720387057916007218863/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_13_s50

theorem source_error_18_13_9 : Y 18 13 9 = (-141645844790470070219169/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_13_s50

theorem source_error_18_13_11 : Y 18 13 11 = (241267392281008969222347/819200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_11_13_s50

theorem source_error_18_15_1 : Y 18 15 1 = (-58408977661685586058262139/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_15_s50

theorem source_error_18_15_3 : Y 18 15 3 = (856489912851915268585659/327680000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_15_s50

theorem source_error_18_15_5 : Y 18 15 5 = (166478085484275751174989/262144000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_15_s50

theorem source_error_18_15_7 : Y 18 15 7 = (-293804443074929463225549/655360000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_15_s50

theorem source_error_18_15_9 : Y 18 15 9 = (-70438571087878610696079/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_15_s50

theorem source_error_18_15_11 : Y 18 15 11 = (153598002652096074585513/81920000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_11_15_s50

theorem source_error_18_15_13 : Y 18 15 13 = (-32035926190597582065813/16384000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_13_15_s50

theorem source_error_18_17_1 : Y 18 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_17_s50

theorem source_error_18_17_3 : Y 18 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_17_s50

theorem source_error_18_17_5 : Y 18 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_17_s50

theorem source_error_18_17_7 : Y 18 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_17_s50

theorem source_error_18_17_9 : Y 18 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_17_s50

theorem source_error_18_17_11 : Y 18 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_11_17_s50

theorem source_error_18_17_13 : Y 18 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_13_17_s50

theorem source_error_18_17_15 : Y 18 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_15_17_s50

theorem error_18 : errorRational 18 = candidateY_18 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_18_1_1_s50
  · exact source_error_18_1_3_s50
  · exact source_error_18_1_5_s50
  · exact source_error_18_1_7_s50
  · exact source_error_18_1_9_s50
  · exact source_error_18_1_11_s50
  · exact source_error_18_1_13_s50
  · exact source_error_18_1_15_s50
  · exact source_error_18_1_17_s50
  · exact source_error_18_3_1
  · exact source_error_18_3_3_s50
  · exact source_error_18_3_5_s50
  · exact source_error_18_3_7_s50
  · exact source_error_18_3_9_s50
  · exact source_error_18_3_11_s50
  · exact source_error_18_3_13_s50
  · exact source_error_18_3_15_s50
  · exact source_error_18_3_17_s50
  · exact source_error_18_5_1
  · exact source_error_18_5_3
  · exact source_error_18_5_5_s50
  · exact source_error_18_5_7_s50
  · exact source_error_18_5_9_s50
  · exact source_error_18_5_11_s50
  · exact source_error_18_5_13_s50
  · exact source_error_18_5_15_s50
  · exact source_error_18_5_17_s50
  · exact source_error_18_7_1
  · exact source_error_18_7_3
  · exact source_error_18_7_5
  · exact source_error_18_7_7_s50
  · exact source_error_18_7_9_s50
  · exact source_error_18_7_11_s50
  · exact source_error_18_7_13_s50
  · exact source_error_18_7_15_s50
  · exact source_error_18_7_17_s50
  · exact source_error_18_9_1
  · exact source_error_18_9_3
  · exact source_error_18_9_5
  · exact source_error_18_9_7
  · exact source_error_18_9_9_s50
  · exact source_error_18_9_11_s50
  · exact source_error_18_9_13_s50
  · exact source_error_18_9_15_s50
  · exact source_error_18_9_17_s50
  · exact source_error_18_11_1
  · exact source_error_18_11_3
  · exact source_error_18_11_5
  · exact source_error_18_11_7
  · exact source_error_18_11_9
  · exact source_error_18_11_11_s50
  · exact source_error_18_11_13_s50
  · exact source_error_18_11_15_s50
  · exact source_error_18_11_17_s50
  · exact source_error_18_13_1
  · exact source_error_18_13_3
  · exact source_error_18_13_5
  · exact source_error_18_13_7
  · exact source_error_18_13_9
  · exact source_error_18_13_11
  · exact source_error_18_13_13_s50
  · exact source_error_18_13_15_s50
  · exact source_error_18_13_17_s50
  · exact source_error_18_15_1
  · exact source_error_18_15_3
  · exact source_error_18_15_5
  · exact source_error_18_15_7
  · exact source_error_18_15_9
  · exact source_error_18_15_11
  · exact source_error_18_15_13
  · exact source_error_18_15_15_s50
  · exact source_error_18_15_17_s50
  · exact source_error_18_17_1
  · exact source_error_18_17_3
  · exact source_error_18_17_5
  · exact source_error_18_17_7
  · exact source_error_18_17_9
  · exact source_error_18_17_11
  · exact source_error_18_17_13
  · exact source_error_18_17_15
  · exact source_error_18_17_17_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_18_s50_oai : compressedRational 18 =
    lower_18 * Matrix.diagonal pivots_18 * lower_18.transpose := by
  rw [compressedRational_eq_compute, error_18, gram_18_s50]
  exact candidateLDL_18_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_18_s50_oai := @OAI.Laughlin.Certificate.ldl_18_s50_oai
