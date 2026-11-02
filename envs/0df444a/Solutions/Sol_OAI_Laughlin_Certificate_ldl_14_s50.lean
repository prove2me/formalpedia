-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_14_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:26:08.629505+00:00
-- url     : https://prove2.me/submissions/58dd3e34-70d3-43aa-9fc6-b6d62b6461fd

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_14_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_14_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_14_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_14_3_1 : Y 14 3 1 = (-99652836936417746642331957/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_3_s50

theorem source_error_14_5_1 : Y 14 5 1 = (198343656225197394663337443/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_5_s50

theorem source_error_14_5_3 : Y 14 5 3 = (-347065711842922353039231/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_5_s50

theorem source_error_14_7_1 : Y 14 7 1 = (-10805495312804179528323783/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_7_s50

theorem source_error_14_7_3 : Y 14 7 3 = (-138985253242272601987977/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_7_s50

theorem source_error_14_7_5 : Y 14 7 5 = (1776603855966711095862153/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_7_s50

theorem source_error_14_9_1 : Y 14 9 1 = (21398938288605875882996397/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_9_s50

theorem source_error_14_9_3 : Y 14 9 3 = (-567150585351068471238783/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_9_s50

theorem source_error_14_9_5 : Y 14 9 5 = (932798387166894000074907/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_9_s50

theorem source_error_14_9_7 : Y 14 9 7 = (1701251773125333268329/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_7_9_s50

theorem source_error_14_11_1 : Y 14 11 1 = (3160468299521670425437149/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_11_s50

theorem source_error_14_11_3 : Y 14 11 3 = (-141724874857705188581763/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_11_s50

theorem source_error_14_11_5 : Y 14 11 5 = (269131392507015595229211/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_11_s50

theorem source_error_14_11_7 : Y 14 11 7 = (-41108078112253038740007/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_7_11_s50

theorem source_error_14_11_9 : Y 14 11 9 = (56731873890489317051103/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_9_11_s50

theorem source_error_14_13_1 : Y 14 13 1 = (-12750872962864833675394659/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_13_s50

theorem source_error_14_13_3 : Y 14 13 3 = (-841622022843306152134401/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_13_s50

theorem source_error_14_13_5 : Y 14 13 5 = (6370357421543107418633493/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_13_s50

theorem source_error_14_13_7 : Y 14 13 7 = (-1332400286315383367619537/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_7_13_s50

theorem source_error_14_13_9 : Y 14 13 9 = (702921905295609015979677/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_9_13_s50

theorem source_error_14_13_11 : Y 14 13 11 = (-304589521531696266272979/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_11_13_s50

theorem error_14 : errorRational 14 = candidateY_14 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_14_1_1_s50
  · exact source_error_14_1_3_s50
  · exact source_error_14_1_5_s50
  · exact source_error_14_1_7_s50
  · exact source_error_14_1_9_s50
  · exact source_error_14_1_11_s50
  · exact source_error_14_1_13_s50
  · exact source_error_14_3_1
  · exact source_error_14_3_3_s50
  · exact source_error_14_3_5_s50
  · exact source_error_14_3_7_s50
  · exact source_error_14_3_9_s50
  · exact source_error_14_3_11_s50
  · exact source_error_14_3_13_s50
  · exact source_error_14_5_1
  · exact source_error_14_5_3
  · exact source_error_14_5_5_s50
  · exact source_error_14_5_7_s50
  · exact source_error_14_5_9_s50
  · exact source_error_14_5_11_s50
  · exact source_error_14_5_13_s50
  · exact source_error_14_7_1
  · exact source_error_14_7_3
  · exact source_error_14_7_5
  · exact source_error_14_7_7_s50
  · exact source_error_14_7_9_s50
  · exact source_error_14_7_11_s50
  · exact source_error_14_7_13_s50
  · exact source_error_14_9_1
  · exact source_error_14_9_3
  · exact source_error_14_9_5
  · exact source_error_14_9_7
  · exact source_error_14_9_9_s50
  · exact source_error_14_9_11_s50
  · exact source_error_14_9_13_s50
  · exact source_error_14_11_1
  · exact source_error_14_11_3
  · exact source_error_14_11_5
  · exact source_error_14_11_7
  · exact source_error_14_11_9
  · exact source_error_14_11_11_s50
  · exact source_error_14_11_13_s50
  · exact source_error_14_13_1
  · exact source_error_14_13_3
  · exact source_error_14_13_5
  · exact source_error_14_13_7
  · exact source_error_14_13_9
  · exact source_error_14_13_11
  · exact source_error_14_13_13_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_14_s50_oai : compressedRational 14 =
    lower_14 * Matrix.diagonal pivots_14 * lower_14.transpose := by
  rw [compressedRational_eq_compute, error_14, gram_14_s50]
  exact candidateLDL_14_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_14_s50_oai := @OAI.Laughlin.Certificate.ldl_14_s50_oai
