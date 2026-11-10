-- Prove2me | solution 1 for OAI.SharpPlanar.pieceBase_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:21:24.091443+00:00
-- url     : https://prove2.me/submissions/b7f49927-4957-4863-a224-c6600d92bc18

import Mathlib
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_dampingCap_pos_g
import Theorems.Thm_OAI_SharpPlanar_pieceBase_pos_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis
lemma pieceBase_contains_g_oai (j : Fin 6) :
    Real.exp (-(314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩) ≤ pieceBase j := by
  have hg : 0 ≤ (314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩ := by
    exact mul_nonneg (by norm_num) (dampingCap_pos_g _).le
  have hp := Real.sum_le_exp_of_nonneg hg 20
  rw [neg_mul,Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  have ht : 1 ≤ pieceBase j * (∑ i ∈ Finset.range 20,
      ((314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩)^i/(i.factorial:ℝ)) := by
    fin_cases j <;> (first | (simp [pieceBase,dampingCap,Finset.sum_range_succ]; all_goals first | (norm_num [pieceBase,dampingCap,Finset.sum_range_succ]; done) | rfl | decide) | (norm_num [pieceBase,dampingCap,Finset.sum_range_succ]; done) | norm_num [pieceBase,dampingCap,Finset.sum_range_succ])
  exact ht.trans (mul_le_mul_of_nonneg_left hp (pieceBase_pos_g j).le)

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.pieceBase_contains_g_oai := @OAI.SharpPlanar.pieceBase_contains_g_oai
