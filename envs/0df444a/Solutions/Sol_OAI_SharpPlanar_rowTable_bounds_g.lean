-- Prove2me | solution 1 for OAI.SharpPlanar.rowTable_bounds_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:23.871289+00:00
-- url     : https://prove2.me/submissions/7fd70028-2ac4-41c7-9d7a-462a5307641e

import Mathlib
import Definitions.Def_OAIQ098G379
import Theorems.Thm_OAI_SharpPlanar_rowTable_le_g
import Theorems.Thm_OAI_SharpPlanar_tableRational_hundred_g
import Theorems.Thm_OAI_SharpPlanar_tableRational_sixteen_g

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

lemma tableRational_zero : tableRational 0 < 28 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]
lemma tableRational_four : tableRational 4 < 28/100 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]

theorem rowTable_bounds_g_oai : rowTable 0 < 28 ∧ rowTable 4 < 28/100 ∧
    rowTable 16 < 15/1000 ∧ rowTable 100 < 5/10^10 :=
  ⟨(rowTable_le_g 0).trans_lt tableRational_zero,(rowTable_le_g 4).trans_lt tableRational_four,
    (rowTable_le_g 16).trans_lt tableRational_sixteen_g,(rowTable_le_g 100).trans_lt tableRational_hundred_g⟩
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.rowTable_bounds_g_oai := @OAI.SharpPlanar.rowTable_bounds_g_oai
