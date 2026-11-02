-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_certificates_s50
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:05:42.363715+00:00
-- url     : https://prove2.me/submissions/03bcee49-4887-4064-bf34-ea1ee2dea3d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_10_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_11_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_12_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_13_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_14_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_15_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_16_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_17_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_18_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_19_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_20_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_21_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_22_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_23_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_9_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_five_positive_s50
import Theorems.Thm_OAI_Laughlin_Certificate_ldl_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_ldl_8_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_RationalPSD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem rational_ldl_positive {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) (h : A = L * Matrix.diagonal d * L.transpose)
    (hd : ∀ i, 0 ≤ d i) : (A.map (Rat.castHom ℝ)).PosSemidef := by
  rw [h, Matrix.map_mul, Matrix.map_mul]
  have hdiag : (Matrix.diagonal d).map (Rat.castHom ℝ) =
      Matrix.diagonal (fun i => (d i : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have htrans : L.transpose.map (Rat.castHom ℝ) =
      (L.map (Rat.castHom ℝ)).conjTranspose := by
    ext i j
    simp
  rw [hdiag, htrans]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℝ) ≤ (d i : ℝ)
  exact_mod_cast hd i

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem compressed_positive_of_gram_zero (D : ℕ) (h : gramRational D = 0) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  have he : compressedRational D = 0 := by simp [compressedRational, h]
  rw [he]
  simpa using (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ).PosSemidef)


theorem gram_one_zero : gramRational 1 = 0 := by decide +kernel
theorem gram_two_zero : gramRational 2 = 0 := by decide +kernel
theorem gram_three_zero : gramRational 3 = 0 := by decide +kernel
theorem gram_four_zero : gramRational 4 = 0 := by decide +kernel
theorem gram_six_zero : gramRational 6 = 0 := by decide +kernel

theorem zero_blocks_positive (D : ℕ) (hD : D ∈ [1,2,3,4,6]) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl
  · exact compressed_positive_of_gram_zero 1 gram_one_zero
  · exact compressed_positive_of_gram_zero 2 gram_two_zero
  · exact compressed_positive_of_gram_zero 3 gram_three_zero
  · exact compressed_positive_of_gram_zero 4 gram_four_zero
  · exact compressed_positive_of_gram_zero 6 gram_six_zero

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem four_body_7_positive :
    ((compressedRational 7).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_7 pivots_7 ldl_7_s50
  intro i
  fin_cases i <;> norm_num [pivots_7]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem four_body_8_positive :
    ((compressedRational 8).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_8 pivots_8 ldl_8_s50
  intro i
  fin_cases i <;> norm_num [pivots_8]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_All
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem four_body_certificates_s50_oai (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef := by
  interval_cases D
  · exact zero_blocks_positive 1 (by decide)
  · exact zero_blocks_positive 2 (by decide)
  · exact zero_blocks_positive 3 (by decide)
  · exact zero_blocks_positive 4 (by decide)
  · exact four_body_five_positive_s50
  · exact zero_blocks_positive 6 (by decide)
  · exact four_body_7_positive
  · exact four_body_8_positive
  · exact four_body_9_positive_s50
  · exact four_body_10_positive_s50
  · exact four_body_11_positive_s50
  · exact four_body_12_positive_s50
  · exact four_body_13_positive_s50
  · exact four_body_14_positive_s50
  · exact four_body_15_positive_s50
  · exact four_body_16_positive_s50
  · exact four_body_17_positive_s50
  · exact four_body_18_positive_s50
  · exact four_body_19_positive_s50
  · exact four_body_20_positive_s50
  · exact four_body_21_positive_s50
  · exact four_body_22_positive_s50
  · exact four_body_23_positive_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_certificates_s50_oai := @OAI.Laughlin.Certificate.four_body_certificates_s50_oai
