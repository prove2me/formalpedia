-- Prove2me | solution 1 for OAI.SharpPlanar.atomBase_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:33.118597+00:00
-- url     : https://prove2.me/submissions/e3f4276e-bd43-4175-9260-1f13f41064ee

import Mathlib
import Definitions.Def_OAIQ098G362
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_atomBase_pos_g
import Theorems.Thm_OAI_SharpPlanar_dampingCap_pos_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
lemma atomBase_contains_g_oai (j : Fin 7) : Real.exp (-(314159/100000:ℝ)*dampingCap j) ≤ atomBase j := by
  have hp := Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤314159/100000) (dampingCap_pos_g j).le) 30
  rw [neg_mul,Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  have ht : 1 ≤ atomBase j*(∑ i ∈ Finset.range 30,((314159/100000:ℝ)*dampingCap j)^i/(i.factorial:ℝ)) := by
    fin_cases j <;> (first | (simp [atomBase,dampingCap,Finset.sum_range_succ]; all_goals first | (norm_num [atomBase,dampingCap,Finset.sum_range_succ]; done) | rfl | decide) | (norm_num [atomBase,dampingCap,Finset.sum_range_succ]; done) | norm_num [atomBase,dampingCap,Finset.sum_range_succ])
  exact ht.trans (mul_le_mul_of_nonneg_left hp (atomBase_pos_g j).le)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atomBase_contains_g_oai := @OAI.SharpPlanar.atomBase_contains_g_oai
