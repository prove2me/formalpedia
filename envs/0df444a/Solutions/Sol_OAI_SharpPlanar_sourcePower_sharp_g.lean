-- Prove2me | solution 1 for OAI.SharpPlanar.sourcePower_sharp_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T22:34:47.47775+00:00
-- url     : https://prove2.me/submissions/241b5037-0411-4bc2-ac4f-76422a43cb09

import Mathlib
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1690
import Definitions.Def_OAIQ098G1695
import Theorems.Thm_OAI_SharpPlanar_normalizedH_table_g
import Theorems.Thm_OAI_SharpPlanar_table_jet_sharp_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoarseTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma sourcePower_sharp_g_oai (a : Bool) (n : ℕ) (y : ℝ) (nu r : ℕ) :
    |sourcePower a n y nu r| ≤ |y|^r*sharpTaylor (r+nu) n/((r+nu).factorial:ℝ) := by
  rw [sourcePower,normalizedH_table_g,abs_mul,abs_mul,abs_pow,abs_div,abs_of_nonneg (Nat.cast_nonneg ((r+nu).factorial) : (0:ℝ)≤((r+nu).factorial:ℝ))]
  have ha : |(if a then (1:ℝ) else -1)|=1 := by cases a <;> norm_num
  rw [ha,one_mul,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (table_jet_sharp_g a (r+nu) n) (Nat.cast_nonneg _)) (pow_nonneg (abs_nonneg _) _)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.sourcePower_sharp_g_oai := @OAI.SharpPlanar.sourcePower_sharp_g_oai
