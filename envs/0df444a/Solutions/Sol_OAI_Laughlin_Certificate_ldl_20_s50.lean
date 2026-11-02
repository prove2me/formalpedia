-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_20_s50
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:31:22.272946+00:00
-- url     : https://prove2.me/submissions/a6f9d3d6-2b3a-411e-ad96-1e6f9e72e996
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_20_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_20_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_20_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_20_3_1 : Y 20 3 1 = (21667622927027497262745903/204800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_3_s50

theorem source_error_20_5_1 : Y 20 5 1 = (-11712315275254254792460329/327680000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_5_s50

theorem source_error_20_5_3 : Y 20 5 3 = (1943037668945799386453493/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_5_s50

theorem source_error_20_7_1 : Y 20 7 1 = (665376664948039201360203/40960000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_7_s50

theorem source_error_20_7_3 : Y 20 7 3 = (-1013982585631618048647201/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_7_s50

theorem source_error_20_7_5 : Y 20 7 5 = (97684912586085571093347/32768000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_5_7_s50

theorem source_error_20_9_1 : Y 20 9 1 = (-316262058979922913891033/40960000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_9_s50

theorem source_error_20_9_3 : Y 20 9 3 = (30613754919741298283979/10240000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_9_s50

theorem source_error_20_9_5 : Y 20 9 5 = (-11858364672253510424013/8192000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_5_9_s50

theorem source_error_20_9_7 : Y 20 9 7 = (333816883149802681629/409600000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_7_9_s50

theorem source_error_20_11_1 : Y 20 11 1 = (5363979077413683764037/25600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_11_s50

theorem source_error_20_11_3 : Y 20 11 3 = (107082038149227953680869/102400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_11_s50

theorem source_error_20_11_5 : Y 20 11 5 = (-14013038479459638758139/20480000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_5_11_s50

theorem source_error_20_11_7 : Y 20 11 7 = (8819254098389714698719/20480000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_7_11_s50

theorem source_error_20_11_9 : Y 20 11 9 = (-272920889814962733729/1280000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_9_11_s50

theorem source_error_20_13_1 : Y 20 13 1 = (1356924469605003889899309/102400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_13_s50

theorem source_error_20_13_3 : Y 20 13 3 = (-520977417754125297368403/51200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_13_s50

theorem source_error_20_13_5 : Y 20 13 5 = (117196994897535165704091/20480000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_5_13_s50

theorem source_error_20_13_7 : Y 20 13 7 = (-35062147478835063928341/10240000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_7_13_s50

theorem source_error_20_13_9 : Y 20 13 9 = (4300425691175779286121/2560000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_9_13_s50

theorem source_error_20_13_11 : Y 20 13 11 = (7072091643721157882829/6400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_11_13_s50

theorem source_error_20_15_1 : Y 20 15 1 = (-99760004425375579574289/2560000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_15_s50

theorem source_error_20_15_3 : Y 20 15 3 = (304457703228940211619669/10240000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_15_s50

theorem source_error_20_15_5 : Y 20 15 5 = (-34211653005025978665183/2048000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_5_15_s50

theorem source_error_20_15_7 : Y 20 15 7 = (20460760081953150590631/2048000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_7_15_s50

theorem source_error_20_15_9 : Y 20 15 9 = (-627014474788464764001/128000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_9_15_s50

theorem source_error_20_15_11 : Y 20 15 11 = (-4132909998582898800267/1280000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_11_15_s50

theorem source_error_20_15_13 : Y 20 15 13 = (15026634633786455969289/640000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_13_15_s50

theorem source_error_20_17_1 : Y 20 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_17_s50

theorem source_error_20_17_3 : Y 20 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_17_s50

theorem source_error_20_17_5 : Y 20 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_5_17_s50

theorem source_error_20_17_7 : Y 20 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_7_17_s50

theorem source_error_20_17_9 : Y 20 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_9_17_s50

theorem source_error_20_17_11 : Y 20 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_11_17_s50

theorem source_error_20_17_13 : Y 20 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_13_17_s50

theorem source_error_20_17_15 : Y 20 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_15_17_s50

theorem source_error_20_19_1 : Y 20 19 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_1_19_s50

theorem source_error_20_19_3 : Y 20 19 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_3_19_s50

theorem source_error_20_19_5 : Y 20 19 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_5_19_s50

theorem source_error_20_19_7 : Y 20 19 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_7_19_s50

theorem source_error_20_19_9 : Y 20 19 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_9_19_s50

theorem source_error_20_19_11 : Y 20 19 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_11_19_s50

theorem source_error_20_19_13 : Y 20 19 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_13_19_s50

theorem source_error_20_19_15 : Y 20 19 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_15_19_s50

theorem source_error_20_19_17 : Y 20 19 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_20_17_19_s50

theorem error_20 : errorRational 20 = candidateY_20 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_20_1_1_s50
  · exact source_error_20_1_3_s50
  · exact source_error_20_1_5_s50
  · exact source_error_20_1_7_s50
  · exact source_error_20_1_9_s50
  · exact source_error_20_1_11_s50
  · exact source_error_20_1_13_s50
  · exact source_error_20_1_15_s50
  · exact source_error_20_1_17_s50
  · exact source_error_20_1_19_s50
  · exact source_error_20_3_1
  · exact source_error_20_3_3_s50
  · exact source_error_20_3_5_s50
  · exact source_error_20_3_7_s50
  · exact source_error_20_3_9_s50
  · exact source_error_20_3_11_s50
  · exact source_error_20_3_13_s50
  · exact source_error_20_3_15_s50
  · exact source_error_20_3_17_s50
  · exact source_error_20_3_19_s50
  · exact source_error_20_5_1
  · exact source_error_20_5_3
  · exact source_error_20_5_5_s50
  · exact source_error_20_5_7_s50
  · exact source_error_20_5_9_s50
  · exact source_error_20_5_11_s50
  · exact source_error_20_5_13_s50
  · exact source_error_20_5_15_s50
  · exact source_error_20_5_17_s50
  · exact source_error_20_5_19_s50
  · exact source_error_20_7_1
  · exact source_error_20_7_3
  · exact source_error_20_7_5
  · exact source_error_20_7_7_s50
  · exact source_error_20_7_9_s50
  · exact source_error_20_7_11_s50
  · exact source_error_20_7_13_s50
  · exact source_error_20_7_15_s50
  · exact source_error_20_7_17_s50
  · exact source_error_20_7_19_s50
  · exact source_error_20_9_1
  · exact source_error_20_9_3
  · exact source_error_20_9_5
  · exact source_error_20_9_7
  · exact source_error_20_9_9_s50
  · exact source_error_20_9_11_s50
  · exact source_error_20_9_13_s50
  · exact source_error_20_9_15_s50
  · exact source_error_20_9_17_s50
  · exact source_error_20_9_19_s50
  · exact source_error_20_11_1
  · exact source_error_20_11_3
  · exact source_error_20_11_5
  · exact source_error_20_11_7
  · exact source_error_20_11_9
  · exact source_error_20_11_11_s50
  · exact source_error_20_11_13_s50
  · exact source_error_20_11_15_s50
  · exact source_error_20_11_17_s50
  · exact source_error_20_11_19_s50
  · exact source_error_20_13_1
  · exact source_error_20_13_3
  · exact source_error_20_13_5
  · exact source_error_20_13_7
  · exact source_error_20_13_9
  · exact source_error_20_13_11
  · exact source_error_20_13_13_s50
  · exact source_error_20_13_15_s50
  · exact source_error_20_13_17_s50
  · exact source_error_20_13_19_s50
  · exact source_error_20_15_1
  · exact source_error_20_15_3
  · exact source_error_20_15_5
  · exact source_error_20_15_7
  · exact source_error_20_15_9
  · exact source_error_20_15_11
  · exact source_error_20_15_13
  · exact source_error_20_15_15_s50
  · exact source_error_20_15_17_s50
  · exact source_error_20_15_19_s50
  · exact source_error_20_17_1
  · exact source_error_20_17_3
  · exact source_error_20_17_5
  · exact source_error_20_17_7
  · exact source_error_20_17_9
  · exact source_error_20_17_11
  · exact source_error_20_17_13
  · exact source_error_20_17_15
  · exact source_error_20_17_17_s50
  · exact source_error_20_17_19_s50
  · exact source_error_20_19_1
  · exact source_error_20_19_3
  · exact source_error_20_19_5
  · exact source_error_20_19_7
  · exact source_error_20_19_9
  · exact source_error_20_19_11
  · exact source_error_20_19_13
  · exact source_error_20_19_15
  · exact source_error_20_19_17
  · exact source_error_20_19_19_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_20_s50_oai : compressedRational 20 =
    lower_20 * Matrix.diagonal pivots_20 * lower_20.transpose := by
  rw [compressedRational_eq_compute, error_20, gram_20_s50]
  exact candidateLDL_20_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_20_s50_oai := @OAI.Laughlin.Certificate.ldl_20_s50_oai
