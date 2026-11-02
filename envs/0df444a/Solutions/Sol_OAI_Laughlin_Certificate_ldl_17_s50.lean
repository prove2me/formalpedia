-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:28:33.214068+00:00
-- url     : https://prove2.me/submissions/68a700d5-6765-4d18-89f1-8261e0e75658

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_17_3_1 : Y 17 3 1 = (-34150355623889743675914477/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_3_s50

theorem source_error_17_5_1 : Y 17 5 1 = (260924265129905899387586721/83886080000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_5_s50

theorem source_error_17_5_3 : Y 17 5 3 = (10972785710270109216153663/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_5_s50

theorem source_error_17_7_1 : Y 17 7 1 = (-67528457531024325424642053/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_7_s50

theorem source_error_17_7_3 : Y 17 7 3 = (-408068525315759942414781/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_7_s50

theorem source_error_17_7_5 : Y 17 7 5 = (4351689332062192591003071/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_7_s50

theorem source_error_17_9_1 : Y 17 9 1 = (-30137637143983305054521403/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_9_s50

theorem source_error_17_9_3 : Y 17 9 3 = (729849806595543331244547/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_9_s50

theorem source_error_17_9_5 : Y 17 9 5 = (83301302217472013622717/10485760000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_9_s50

theorem source_error_17_9_7 : Y 17 9 7 = (138574461584170298662731/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_9_s50

theorem source_error_17_11_1 : Y 17 11 1 = (95166999960067286140262373/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_11_s50

theorem source_error_17_11_3 : Y 17 11 3 = (11113201543710491752527/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_11_s50

theorem source_error_17_11_5 : Y 17 11 5 = (-203973650747133817508343/1048576000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_11_s50

theorem source_error_17_11_7 : Y 17 11 7 = (322312699672503215100579/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_11_s50

theorem source_error_17_11_9 : Y 17 11 9 = (1543576781120216089401/131072000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_11_s50

theorem source_error_17_13_1 : Y 17 13 1 = (-175538440354363800262225677/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_13_s50

theorem source_error_17_13_3 : Y 17 13 3 = (-12885057439514659527475347/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_13_s50

theorem source_error_17_13_5 : Y 17 13 5 = (16866893128958580992747463/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_13_s50

theorem source_error_17_13_7 : Y 17 13 7 = (-5414374042135146758937267/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_13_s50

theorem source_error_17_13_9 : Y 17 13 9 = (727025046163822366323363/16384000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_13_s50

theorem source_error_17_13_11 : Y 17 13 11 = (1054078060656605687920503/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_11_13_s50

theorem source_error_17_15_1 : Y 17 15 1 = (69154353838247955125781933/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_15_s50

theorem source_error_17_15_3 : Y 17 15 3 = (1281998470570534260875331/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_15_s50

theorem source_error_17_15_5 : Y 17 15 5 = (-99471136192512553900431/104857600000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_15_s50

theorem source_error_17_15_7 : Y 17 15 7 = (53455862611083189243987/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_15_s50

theorem source_error_17_15_9 : Y 17 15 9 = (948970636189602992298333/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_15_s50

theorem source_error_17_15_11 : Y 17 15 11 = (-99701519947816820212179/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_11_15_s50

theorem source_error_17_15_13 : Y 17 15 13 = (797255391734832796032267/819200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_13_15_s50

theorem source_error_17_17_1 : Y 17 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_17_s50

theorem source_error_17_17_3 : Y 17 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_17_s50

theorem source_error_17_17_5 : Y 17 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_17_s50

theorem source_error_17_17_7 : Y 17 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_17_s50

theorem source_error_17_17_9 : Y 17 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_17_s50

theorem source_error_17_17_11 : Y 17 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_11_17_s50

theorem source_error_17_17_13 : Y 17 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_13_17_s50

theorem source_error_17_17_15 : Y 17 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_15_17_s50

theorem error_17 : errorRational 17 = candidateY_17 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_17_1_1_s50
  · exact source_error_17_1_3_s50
  · exact source_error_17_1_5_s50
  · exact source_error_17_1_7_s50
  · exact source_error_17_1_9_s50
  · exact source_error_17_1_11_s50
  · exact source_error_17_1_13_s50
  · exact source_error_17_1_15_s50
  · exact source_error_17_1_17_s50
  · exact source_error_17_3_1
  · exact source_error_17_3_3_s50
  · exact source_error_17_3_5_s50
  · exact source_error_17_3_7_s50
  · exact source_error_17_3_9_s50
  · exact source_error_17_3_11_s50
  · exact source_error_17_3_13_s50
  · exact source_error_17_3_15_s50
  · exact source_error_17_3_17_s50
  · exact source_error_17_5_1
  · exact source_error_17_5_3
  · exact source_error_17_5_5_s50
  · exact source_error_17_5_7_s50
  · exact source_error_17_5_9_s50
  · exact source_error_17_5_11_s50
  · exact source_error_17_5_13_s50
  · exact source_error_17_5_15_s50
  · exact source_error_17_5_17_s50
  · exact source_error_17_7_1
  · exact source_error_17_7_3
  · exact source_error_17_7_5
  · exact source_error_17_7_7_s50
  · exact source_error_17_7_9_s50
  · exact source_error_17_7_11_s50
  · exact source_error_17_7_13_s50
  · exact source_error_17_7_15_s50
  · exact source_error_17_7_17_s50
  · exact source_error_17_9_1
  · exact source_error_17_9_3
  · exact source_error_17_9_5
  · exact source_error_17_9_7
  · exact source_error_17_9_9_s50
  · exact source_error_17_9_11_s50
  · exact source_error_17_9_13_s50
  · exact source_error_17_9_15_s50
  · exact source_error_17_9_17_s50
  · exact source_error_17_11_1
  · exact source_error_17_11_3
  · exact source_error_17_11_5
  · exact source_error_17_11_7
  · exact source_error_17_11_9
  · exact source_error_17_11_11_s50
  · exact source_error_17_11_13_s50
  · exact source_error_17_11_15_s50
  · exact source_error_17_11_17_s50
  · exact source_error_17_13_1
  · exact source_error_17_13_3
  · exact source_error_17_13_5
  · exact source_error_17_13_7
  · exact source_error_17_13_9
  · exact source_error_17_13_11
  · exact source_error_17_13_13_s50
  · exact source_error_17_13_15_s50
  · exact source_error_17_13_17_s50
  · exact source_error_17_15_1
  · exact source_error_17_15_3
  · exact source_error_17_15_5
  · exact source_error_17_15_7
  · exact source_error_17_15_9
  · exact source_error_17_15_11
  · exact source_error_17_15_13
  · exact source_error_17_15_15_s50
  · exact source_error_17_15_17_s50
  · exact source_error_17_17_1
  · exact source_error_17_17_3
  · exact source_error_17_17_5
  · exact source_error_17_17_7
  · exact source_error_17_17_9
  · exact source_error_17_17_11
  · exact source_error_17_17_13
  · exact source_error_17_17_15
  · exact source_error_17_17_17_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_17_s50_oai : compressedRational 17 =
    lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose := by
  rw [compressedRational_eq_compute, error_17, gram_17_s50]
  exact candidateLDL_17_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_17_s50_oai := @OAI.Laughlin.Certificate.ldl_17_s50_oai
