-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_21_s50
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:32:10.751982+00:00
-- url     : https://prove2.me/submissions/5e256ad4-6424-4829-8f2c-b8058319e1d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_11_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_13_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_15_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_17_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_19_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_21_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_21_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_21_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_21_3_1 : Y 21 3 1 = (57038851132594341185352177/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_3_s50

theorem source_error_21_5_1 : Y 21 5 1 = (-5636036476590197124447/327680000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_5_s50

theorem source_error_21_5_3 : Y 21 5 3 = (492577388419375083797973/40960000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_5_s50

theorem source_error_21_7_1 : Y 21 7 1 = (-1952083051117812873373113/32768000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_7_s50

theorem source_error_21_7_3 : Y 21 7 3 = (-281862084701495601299997/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_7_s50

theorem source_error_21_7_5 : Y 21 7 5 = (53358620528514863973411/8192000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_7_s50

theorem source_error_21_9_1 : Y 21 9 1 = (418641912860774562758799/4096000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_9_s50

theorem source_error_21_9_3 : Y 21 9 3 = (-57918765188790724575357/20480000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_9_s50

theorem source_error_21_9_5 : Y 21 9 5 = (-6801410828588460561477/1024000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_9_s50

theorem source_error_21_9_7 : Y 21 9 7 = (34389795345971868711909/4096000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_7_9_s50

theorem source_error_21_11_1 : Y 21 11 1 = (-644220666819787412766411/4096000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_11_s50

theorem source_error_21_11_3 : Y 21 11 3 = (143714000293113981147417/20480000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_11_s50

theorem source_error_21_11_5 : Y 21 11 5 = (1665119090212013288853/204800000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_11_s50

theorem source_error_21_11_7 : Y 21 11 7 = (-45427929111821472609393/4096000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_7_11_s50

theorem source_error_21_11_9 : Y 21 11 9 = (7064452961983792435599/512000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_9_11_s50

theorem source_error_21_13_1 : Y 21 13 1 = (1256376941124933712895811/5120000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_13_s50

theorem source_error_21_13_3 : Y 21 13 3 = (-331513340018520454483689/25600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_13_s50

theorem source_error_21_13_5 : Y 21 13 5 = (-14227460106212415583521/1280000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_13_s50

theorem source_error_21_13_7 : Y 21 13 7 = (81562090823302666065489/5120000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_7_13_s50

theorem source_error_21_13_9 : Y 21 13 9 = (-12849900797681178702471/640000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_9_13_s50

theorem source_error_21_13_11 : Y 21 13 11 = (17633221184266489332531/640000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_11_13_s50

theorem source_error_21_15_1 : Y 21 15 1 = (-135618250205634004439631/409600000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_15_s50

theorem source_error_21_15_3 : Y 21 15 3 = (195188481739185067894761/10240000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_15_s50

theorem source_error_21_15_5 : Y 21 15 5 = (7041025764192505558473/512000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_15_s50

theorem source_error_21_15_7 : Y 21 15 7 = (-41788312207893754536033/2048000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_7_15_s50

theorem source_error_21_15_9 : Y 21 15 9 = (6640967897736757856271/256000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_9_15_s50

theorem source_error_21_15_11 : Y 21 15 11 = (-365961031875624676491/10240000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_11_15_s50

theorem source_error_21_15_13 : Y 21 15 13 = (16838009783175354176403/320000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_13_15_s50

theorem source_error_21_17_1 : Y 21 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_17_s50

theorem source_error_21_17_3 : Y 21 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_17_s50

theorem source_error_21_17_5 : Y 21 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_17_s50

theorem source_error_21_17_7 : Y 21 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_7_17_s50

theorem source_error_21_17_9 : Y 21 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_9_17_s50

theorem source_error_21_17_11 : Y 21 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_11_17_s50

theorem source_error_21_17_13 : Y 21 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_13_17_s50

theorem source_error_21_17_15 : Y 21 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_15_17_s50

theorem source_error_21_19_1 : Y 21 19 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_19_s50

theorem source_error_21_19_3 : Y 21 19 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_19_s50

theorem source_error_21_19_5 : Y 21 19 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_19_s50

theorem source_error_21_19_7 : Y 21 19 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_7_19_s50

theorem source_error_21_19_9 : Y 21 19 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_9_19_s50

theorem source_error_21_19_11 : Y 21 19 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_11_19_s50

theorem source_error_21_19_13 : Y 21 19 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_13_19_s50

theorem source_error_21_19_15 : Y 21 19 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_15_19_s50

theorem source_error_21_19_17 : Y 21 19 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_17_19_s50

theorem source_error_21_21_1 : Y 21 21 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_1_21_s50

theorem source_error_21_21_3 : Y 21 21 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_3_21_s50

theorem source_error_21_21_5 : Y 21 21 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_5_21_s50

theorem source_error_21_21_7 : Y 21 21 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_7_21_s50

theorem source_error_21_21_9 : Y 21 21 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_9_21_s50

theorem source_error_21_21_11 : Y 21 21 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_11_21_s50

theorem source_error_21_21_13 : Y 21 21 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_13_21_s50

theorem source_error_21_21_15 : Y 21 21 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_15_21_s50

theorem source_error_21_21_17 : Y 21 21 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_17_21_s50

theorem source_error_21_21_19 : Y 21 21 19 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_21_19_21_s50

theorem error_21 : errorRational 21 = candidateY_21 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_21_1_1_s50
  · exact source_error_21_1_3_s50
  · exact source_error_21_1_5_s50
  · exact source_error_21_1_7_s50
  · exact source_error_21_1_9_s50
  · exact source_error_21_1_11_s50
  · exact source_error_21_1_13_s50
  · exact source_error_21_1_15_s50
  · exact source_error_21_1_17_s50
  · exact source_error_21_1_19_s50
  · exact source_error_21_1_21_s50
  · exact source_error_21_3_1
  · exact source_error_21_3_3_s50
  · exact source_error_21_3_5_s50
  · exact source_error_21_3_7_s50
  · exact source_error_21_3_9_s50
  · exact source_error_21_3_11_s50
  · exact source_error_21_3_13_s50
  · exact source_error_21_3_15_s50
  · exact source_error_21_3_17_s50
  · exact source_error_21_3_19_s50
  · exact source_error_21_3_21_s50
  · exact source_error_21_5_1
  · exact source_error_21_5_3
  · exact source_error_21_5_5_s50
  · exact source_error_21_5_7_s50
  · exact source_error_21_5_9_s50
  · exact source_error_21_5_11_s50
  · exact source_error_21_5_13_s50
  · exact source_error_21_5_15_s50
  · exact source_error_21_5_17_s50
  · exact source_error_21_5_19_s50
  · exact source_error_21_5_21_s50
  · exact source_error_21_7_1
  · exact source_error_21_7_3
  · exact source_error_21_7_5
  · exact source_error_21_7_7_s50
  · exact source_error_21_7_9_s50
  · exact source_error_21_7_11_s50
  · exact source_error_21_7_13_s50
  · exact source_error_21_7_15_s50
  · exact source_error_21_7_17_s50
  · exact source_error_21_7_19_s50
  · exact source_error_21_7_21_s50
  · exact source_error_21_9_1
  · exact source_error_21_9_3
  · exact source_error_21_9_5
  · exact source_error_21_9_7
  · exact source_error_21_9_9_s50
  · exact source_error_21_9_11_s50
  · exact source_error_21_9_13_s50
  · exact source_error_21_9_15_s50
  · exact source_error_21_9_17_s50
  · exact source_error_21_9_19_s50
  · exact source_error_21_9_21_s50
  · exact source_error_21_11_1
  · exact source_error_21_11_3
  · exact source_error_21_11_5
  · exact source_error_21_11_7
  · exact source_error_21_11_9
  · exact source_error_21_11_11_s50
  · exact source_error_21_11_13_s50
  · exact source_error_21_11_15_s50
  · exact source_error_21_11_17_s50
  · exact source_error_21_11_19_s50
  · exact source_error_21_11_21_s50
  · exact source_error_21_13_1
  · exact source_error_21_13_3
  · exact source_error_21_13_5
  · exact source_error_21_13_7
  · exact source_error_21_13_9
  · exact source_error_21_13_11
  · exact source_error_21_13_13_s50
  · exact source_error_21_13_15_s50
  · exact source_error_21_13_17_s50
  · exact source_error_21_13_19_s50
  · exact source_error_21_13_21_s50
  · exact source_error_21_15_1
  · exact source_error_21_15_3
  · exact source_error_21_15_5
  · exact source_error_21_15_7
  · exact source_error_21_15_9
  · exact source_error_21_15_11
  · exact source_error_21_15_13
  · exact source_error_21_15_15_s50
  · exact source_error_21_15_17_s50
  · exact source_error_21_15_19_s50
  · exact source_error_21_15_21_s50
  · exact source_error_21_17_1
  · exact source_error_21_17_3
  · exact source_error_21_17_5
  · exact source_error_21_17_7
  · exact source_error_21_17_9
  · exact source_error_21_17_11
  · exact source_error_21_17_13
  · exact source_error_21_17_15
  · exact source_error_21_17_17_s50
  · exact source_error_21_17_19_s50
  · exact source_error_21_17_21_s50
  · exact source_error_21_19_1
  · exact source_error_21_19_3
  · exact source_error_21_19_5
  · exact source_error_21_19_7
  · exact source_error_21_19_9
  · exact source_error_21_19_11
  · exact source_error_21_19_13
  · exact source_error_21_19_15
  · exact source_error_21_19_17
  · exact source_error_21_19_19_s50
  · exact source_error_21_19_21_s50
  · exact source_error_21_21_1
  · exact source_error_21_21_3
  · exact source_error_21_21_5
  · exact source_error_21_21_7
  · exact source_error_21_21_9
  · exact source_error_21_21_11
  · exact source_error_21_21_13
  · exact source_error_21_21_15
  · exact source_error_21_21_17
  · exact source_error_21_21_19
  · exact source_error_21_21_21_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_21_s50_oai : compressedRational 21 =
    lower_21 * Matrix.diagonal pivots_21 * lower_21.transpose := by
  rw [compressedRational_eq_compute, error_21, gram_21_s50]
  exact candidateLDL_21_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_21_s50_oai := @OAI.Laughlin.Certificate.ldl_21_s50_oai
