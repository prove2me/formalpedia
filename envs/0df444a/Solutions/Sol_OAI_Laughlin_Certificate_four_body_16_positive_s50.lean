-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_16_positive_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:00:49.073172+00:00
-- url     : https://prove2.me/submissions/ab4c0da4-b4b4-4ca3-ae0d-d64f299b2f7a

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_ldl_16_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem four_body_16_positive_s50_oai :
    ((compressedRational 16).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_16 pivots_16 ldl_16_s50
  intro i
  fin_cases i <;> norm_num [pivots_16]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_16_positive_s50_oai := @OAI.Laughlin.Certificate.four_body_16_positive_s50_oai
