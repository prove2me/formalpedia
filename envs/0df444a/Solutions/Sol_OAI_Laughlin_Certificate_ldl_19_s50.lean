-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_19_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:30:09.391671+00:00
-- url     : https://prove2.me/submissions/f42f7278-8b45-4f7c-aefb-f8e2aefc6c03

import Mathlib
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_candidateLDL_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_gram_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_11_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_13_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_15_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_17_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_19_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_13_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_15_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_17_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_19_s50
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_19_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_19_3_1 : Y 19 3 1 = (2702377258995069402702006051/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_3_s50

theorem source_error_19_5_1 : Y 19 5 1 = (-75142211033583596476200627/8388608000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_5_s50

theorem source_error_19_5_3 : Y 19 5 3 = (48289254450191241887451051/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_5_s50

theorem source_error_19_7_1 : Y 19 7 1 = (14766383937965483058974739/4194304000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_7_s50

theorem source_error_19_7_3 : Y 19 7 3 = (-10153357419755611709274627/10485760000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_7_s50

theorem source_error_19_7_5 : Y 19 7 5 = (9278879137014220083120771/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_5_7_s50

theorem source_error_19_9_1 : Y 19 9 1 = (-5511147190592216732622063/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_9_s50

theorem source_error_19_9_3 : Y 19 9 3 = (908184765784913635277259/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_9_s50

theorem source_error_19_9_5 : Y 19 9 5 = (-1279464695992326165509187/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_5_9_s50

theorem source_error_19_9_7 : Y 19 9 7 = (5095867887885096310527/20971520000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_7_9_s50

theorem source_error_19_11_1 : Y 19 11 1 = (7980474838179577610603727/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_11_s50

theorem source_error_19_11_3 : Y 19 11 3 = (-1019757214709519396489379/6553600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_11_s50

theorem source_error_19_11_5 : Y 19 11 5 = (488068742424207599021367/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_5_11_s50

theorem source_error_19_11_7 : Y 19 11 7 = (-66971412540394818930243/262144000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_7_11_s50

theorem source_error_19_11_9 : Y 19 11 9 = (120716948708384445134487/327680000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_9_11_s50

theorem source_error_19_13_1 : Y 19 13 1 = (-114214449015342819092842893/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_13_s50

theorem source_error_19_13_3 : Y 19 13 3 = (11402120818106472624739569/6553600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_13_s50

theorem source_error_19_13_5 : Y 19 13 5 = (-1577990685084360947348949/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_5_13_s50

theorem source_error_19_13_7 : Y 19 13 7 = (423492380929481504822181/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_7_13_s50

theorem source_error_19_13_9 : Y 19 13 9 = (-96794549499067619556357/327680000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_9_13_s50

theorem source_error_19_13_11 : Y 19 13 11 = (429290867351544749347797/819200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_11_13_s50

theorem source_error_19_15_1 : Y 19 15 1 = (15237169390990960795194813/262144000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_15_s50

theorem source_error_19_15_3 : Y 19 15 3 = (-8025292448927789565871341/655360000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_15_s50

theorem source_error_19_15_5 : Y 19 15 5 = (4397077893934901813915277/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_5_15_s50

theorem source_error_19_15_7 : Y 19 15 7 = (-316097984120195393369253/655360000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_7_15_s50

theorem source_error_19_15_9 : Y 19 15 9 = (-152177568634600729759539/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_9_15_s50

theorem source_error_19_15_11 : Y 19 15 11 = (90088259697128585251359/81920000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_11_15_s50

theorem source_error_19_15_13 : Y 19 15 13 = (415758366080515083757131/81920000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_13_15_s50

theorem source_error_19_17_1 : Y 19 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_17_s50

theorem source_error_19_17_3 : Y 19 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_17_s50

theorem source_error_19_17_5 : Y 19 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_5_17_s50

theorem source_error_19_17_7 : Y 19 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_7_17_s50

theorem source_error_19_17_9 : Y 19 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_9_17_s50

theorem source_error_19_17_11 : Y 19 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_11_17_s50

theorem source_error_19_17_13 : Y 19 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_13_17_s50

theorem source_error_19_17_15 : Y 19 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_15_17_s50

theorem source_error_19_19_1 : Y 19 19 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_1_19_s50

theorem source_error_19_19_3 : Y 19 19 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_3_19_s50

theorem source_error_19_19_5 : Y 19 19 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_5_19_s50

theorem source_error_19_19_7 : Y 19 19 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_7_19_s50

theorem source_error_19_19_9 : Y 19 19 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_9_19_s50

theorem source_error_19_19_11 : Y 19 19 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_11_19_s50

theorem source_error_19_19_13 : Y 19 19 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_13_19_s50

theorem source_error_19_19_15 : Y 19 19 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_15_19_s50

theorem source_error_19_19_17 : Y 19 19 17 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_19_17_19_s50

theorem error_19 : errorRational 19 = candidateY_19 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_19_1_1_s50
  · exact source_error_19_1_3_s50
  · exact source_error_19_1_5_s50
  · exact source_error_19_1_7_s50
  · exact source_error_19_1_9_s50
  · exact source_error_19_1_11_s50
  · exact source_error_19_1_13_s50
  · exact source_error_19_1_15_s50
  · exact source_error_19_1_17_s50
  · exact source_error_19_1_19_s50
  · exact source_error_19_3_1
  · exact source_error_19_3_3_s50
  · exact source_error_19_3_5_s50
  · exact source_error_19_3_7_s50
  · exact source_error_19_3_9_s50
  · exact source_error_19_3_11_s50
  · exact source_error_19_3_13_s50
  · exact source_error_19_3_15_s50
  · exact source_error_19_3_17_s50
  · exact source_error_19_3_19_s50
  · exact source_error_19_5_1
  · exact source_error_19_5_3
  · exact source_error_19_5_5_s50
  · exact source_error_19_5_7_s50
  · exact source_error_19_5_9_s50
  · exact source_error_19_5_11_s50
  · exact source_error_19_5_13_s50
  · exact source_error_19_5_15_s50
  · exact source_error_19_5_17_s50
  · exact source_error_19_5_19_s50
  · exact source_error_19_7_1
  · exact source_error_19_7_3
  · exact source_error_19_7_5
  · exact source_error_19_7_7_s50
  · exact source_error_19_7_9_s50
  · exact source_error_19_7_11_s50
  · exact source_error_19_7_13_s50
  · exact source_error_19_7_15_s50
  · exact source_error_19_7_17_s50
  · exact source_error_19_7_19_s50
  · exact source_error_19_9_1
  · exact source_error_19_9_3
  · exact source_error_19_9_5
  · exact source_error_19_9_7
  · exact source_error_19_9_9_s50
  · exact source_error_19_9_11_s50
  · exact source_error_19_9_13_s50
  · exact source_error_19_9_15_s50
  · exact source_error_19_9_17_s50
  · exact source_error_19_9_19_s50
  · exact source_error_19_11_1
  · exact source_error_19_11_3
  · exact source_error_19_11_5
  · exact source_error_19_11_7
  · exact source_error_19_11_9
  · exact source_error_19_11_11_s50
  · exact source_error_19_11_13_s50
  · exact source_error_19_11_15_s50
  · exact source_error_19_11_17_s50
  · exact source_error_19_11_19_s50
  · exact source_error_19_13_1
  · exact source_error_19_13_3
  · exact source_error_19_13_5
  · exact source_error_19_13_7
  · exact source_error_19_13_9
  · exact source_error_19_13_11
  · exact source_error_19_13_13_s50
  · exact source_error_19_13_15_s50
  · exact source_error_19_13_17_s50
  · exact source_error_19_13_19_s50
  · exact source_error_19_15_1
  · exact source_error_19_15_3
  · exact source_error_19_15_5
  · exact source_error_19_15_7
  · exact source_error_19_15_9
  · exact source_error_19_15_11
  · exact source_error_19_15_13
  · exact source_error_19_15_15_s50
  · exact source_error_19_15_17_s50
  · exact source_error_19_15_19_s50
  · exact source_error_19_17_1
  · exact source_error_19_17_3
  · exact source_error_19_17_5
  · exact source_error_19_17_7
  · exact source_error_19_17_9
  · exact source_error_19_17_11
  · exact source_error_19_17_13
  · exact source_error_19_17_15
  · exact source_error_19_17_17_s50
  · exact source_error_19_17_19_s50
  · exact source_error_19_19_1
  · exact source_error_19_19_3
  · exact source_error_19_19_5
  · exact source_error_19_19_7
  · exact source_error_19_19_9
  · exact source_error_19_19_11
  · exact source_error_19_19_13
  · exact source_error_19_19_15
  · exact source_error_19_19_17
  · exact source_error_19_19_19_s50

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_19_s50_oai : compressedRational 19 =
    lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose := by
  rw [compressedRational_eq_compute, error_19, gram_19_s50]
  exact candidateLDL_19_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_19_s50_oai := @OAI.Laughlin.Certificate.ldl_19_s50_oai
