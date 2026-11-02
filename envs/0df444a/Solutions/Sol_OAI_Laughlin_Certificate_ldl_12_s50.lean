-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_12_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:24:32.175042+00:00
-- url     : https://prove2.me/submissions/34f5b32a-de8c-46c5-b405-879841e14d4e

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_12_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_12_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_12_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_12_3_1 : Y 12 3 1 = (7514500960705467759694389/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_3_s50

theorem source_error_12_5_1 : Y 12 5 1 = (3165688667606660909537571/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_5_s50

theorem source_error_12_5_3 : Y 12 5 3 = (13005450739700130750669/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_5_s50

theorem source_error_12_7_1 : Y 12 7 1 = (-41707520784065633150907/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_7_s50

theorem source_error_12_7_3 : Y 12 7 3 = (81483121238154923538567/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_7_s50

theorem source_error_12_7_5 : Y 12 7 5 = (-41483885509932371903727/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_7_s50

theorem source_error_12_9_1 : Y 12 9 1 = (-2287894342236011100448461/10485760000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_9_s50

theorem source_error_12_9_3 : Y 12 9 3 = (404785016635235824043973/5242880000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_9_s50

theorem source_error_12_9_5 : Y 12 9 5 = (-10240121934522536047317/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_9_s50

theorem source_error_12_9_7 : Y 12 9 7 = (-42262827210616968341919/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_7_9_s50

theorem source_error_12_11_1 : Y 12 11 1 = (974459105668097994666249/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_11_s50

theorem source_error_12_11_3 : Y 12 11 3 = (6215584013984995241823/40960000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_11_s50

theorem source_error_12_11_5 : Y 12 11 5 = (-25627330574660171363787/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_11_s50

theorem source_error_12_11_7 : Y 12 11 7 = (102387833991081458685459/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_7_11_s50

theorem source_error_12_11_9 : Y 12 11 9 = (18732467483584451907057/655360000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_9_11_s50

theorem error_12 : errorRational 12 = candidateY_12 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_12_1_1_s50
  · exact source_error_12_1_3_s50
  · exact source_error_12_1_5_s50
  · exact source_error_12_1_7_s50
  · exact source_error_12_1_9_s50
  · exact source_error_12_1_11_s50
  · exact source_error_12_3_1
  · exact source_error_12_3_3_s50
  · exact source_error_12_3_5_s50
  · exact source_error_12_3_7_s50
  · exact source_error_12_3_9_s50
  · exact source_error_12_3_11_s50
  · exact source_error_12_5_1
  · exact source_error_12_5_3
  · exact source_error_12_5_5_s50
  · exact source_error_12_5_7_s50
  · exact source_error_12_5_9_s50
  · exact source_error_12_5_11_s50
  · exact source_error_12_7_1
  · exact source_error_12_7_3
  · exact source_error_12_7_5
  · exact source_error_12_7_7_s50
  · exact source_error_12_7_9_s50
  · exact source_error_12_7_11_s50
  · exact source_error_12_9_1
  · exact source_error_12_9_3
  · exact source_error_12_9_5
  · exact source_error_12_9_7
  · exact source_error_12_9_9_s50
  · exact source_error_12_9_11_s50
  · exact source_error_12_11_1
  · exact source_error_12_11_3
  · exact source_error_12_11_5
  · exact source_error_12_11_7
  · exact source_error_12_11_9
  · exact source_error_12_11_11_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_12_s50_oai : compressedRational 12 =
    lower_12 * Matrix.diagonal pivots_12 * lower_12.transpose := by
  rw [compressedRational_eq_compute, error_12, gram_12_s50]
  exact candidateLDL_12_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_12_s50_oai := @OAI.Laughlin.Certificate.ldl_12_s50_oai
