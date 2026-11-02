-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_16_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:27:44.64552+00:00
-- url     : https://prove2.me/submissions/eb70678e-29e3-4558-8398-de3783a9819c

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_16_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_16_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_16_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_16_3_1 : Y 16 3 1 = (-39034614015379387104670971/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_3_s50

theorem source_error_16_5_1 : Y 16 5 1 = (78202406241711463127687271/83886080000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_5_s50

theorem source_error_16_5_3 : Y 16 5 3 = (2737552373685628655395239/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_5_s50

theorem source_error_16_7_1 : Y 16 7 1 = (23832834670493732956060989/209715200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_7_s50

theorem source_error_16_7_3 : Y 16 7 3 = (22736583113602023500964129/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_7_s50

theorem source_error_16_7_5 : Y 16 7 5 = (1549750421445905525422653/209715200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_7_s50

theorem source_error_16_9_1 : Y 16 9 1 = (22048584820368310367604441/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_9_s50

theorem source_error_16_9_3 : Y 16 9 3 = (1851780972244557042321633/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_9_s50

theorem source_error_16_9_5 : Y 16 9 5 = (-611154627229412014141701/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_9_s50

theorem source_error_16_9_7 : Y 16 9 7 = (1484433801775108633948569/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_9_s50

theorem source_error_16_11_1 : Y 16 11 1 = (2553473034802720354150827/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_11_s50

theorem source_error_16_11_3 : Y 16 11 3 = (507618379345280460543/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_11_s50

theorem source_error_16_11_5 : Y 16 11 5 = (-578745616368603039939/41943040000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_11_s50

theorem source_error_16_11_7 : Y 16 11 7 = (207943103777772680639091/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_11_s50

theorem source_error_16_11_9 : Y 16 11 9 = (-28769175431642817466911/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_9_11_s50

theorem source_error_16_13_1 : Y 16 13 1 = (108255415269241130506236621/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_13_s50

theorem source_error_16_13_3 : Y 16 13 3 = (32584839756386941473215337/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_13_s50

theorem source_error_16_13_5 : Y 16 13 5 = (-64505141078209101647091/1048576000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_13_s50

theorem source_error_16_13_7 : Y 16 13 7 = (-8974467290230038089021529/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_13_s50

theorem source_error_16_13_9 : Y 16 13 9 = (1147904288009241919132977/16384000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_9_13_s50

theorem source_error_16_13_11 : Y 16 13 11 = (189274484540778686288811/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_11_13_s50

theorem source_error_16_15_1 : Y 16 15 1 = (-41435755574383986458435793/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_15_s50

theorem source_error_16_15_3 : Y 16 15 3 = (-12977256793584317385992841/6553600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_15_s50

theorem source_error_16_15_5 : Y 16 15 5 = (-99002192076248555811717/524288000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_15_s50

theorem source_error_16_15_7 : Y 16 15 7 = (4777756237785689667105597/6553600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_15_s50

theorem source_error_16_15_9 : Y 16 15 9 = (68877548037338038801803/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_9_15_s50

theorem source_error_16_15_11 : Y 16 15 11 = (-71581303517955662317887/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_11_15_s50

theorem source_error_16_15_13 : Y 16 15 13 = (384276867404942369454597/819200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_13_15_s50

theorem error_16 : errorRational 16 = candidateY_16 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_16_1_1_s50
  · exact source_error_16_1_3_s50
  · exact source_error_16_1_5_s50
  · exact source_error_16_1_7_s50
  · exact source_error_16_1_9_s50
  · exact source_error_16_1_11_s50
  · exact source_error_16_1_13_s50
  · exact source_error_16_1_15_s50
  · exact source_error_16_3_1
  · exact source_error_16_3_3_s50
  · exact source_error_16_3_5_s50
  · exact source_error_16_3_7_s50
  · exact source_error_16_3_9_s50
  · exact source_error_16_3_11_s50
  · exact source_error_16_3_13_s50
  · exact source_error_16_3_15_s50
  · exact source_error_16_5_1
  · exact source_error_16_5_3
  · exact source_error_16_5_5_s50
  · exact source_error_16_5_7_s50
  · exact source_error_16_5_9_s50
  · exact source_error_16_5_11_s50
  · exact source_error_16_5_13_s50
  · exact source_error_16_5_15_s50
  · exact source_error_16_7_1
  · exact source_error_16_7_3
  · exact source_error_16_7_5
  · exact source_error_16_7_7_s50
  · exact source_error_16_7_9_s50
  · exact source_error_16_7_11_s50
  · exact source_error_16_7_13_s50
  · exact source_error_16_7_15_s50
  · exact source_error_16_9_1
  · exact source_error_16_9_3
  · exact source_error_16_9_5
  · exact source_error_16_9_7
  · exact source_error_16_9_9_s50
  · exact source_error_16_9_11_s50
  · exact source_error_16_9_13_s50
  · exact source_error_16_9_15_s50
  · exact source_error_16_11_1
  · exact source_error_16_11_3
  · exact source_error_16_11_5
  · exact source_error_16_11_7
  · exact source_error_16_11_9
  · exact source_error_16_11_11_s50
  · exact source_error_16_11_13_s50
  · exact source_error_16_11_15_s50
  · exact source_error_16_13_1
  · exact source_error_16_13_3
  · exact source_error_16_13_5
  · exact source_error_16_13_7
  · exact source_error_16_13_9
  · exact source_error_16_13_11
  · exact source_error_16_13_13_s50
  · exact source_error_16_13_15_s50
  · exact source_error_16_15_1
  · exact source_error_16_15_3
  · exact source_error_16_15_5
  · exact source_error_16_15_7
  · exact source_error_16_15_9
  · exact source_error_16_15_11
  · exact source_error_16_15_13
  · exact source_error_16_15_15_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_16_s50_oai : compressedRational 16 =
    lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose := by
  rw [compressedRational_eq_compute, error_16, gram_16_s50]
  exact candidateLDL_16_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_16_s50_oai := @OAI.Laughlin.Certificate.ldl_16_s50_oai
