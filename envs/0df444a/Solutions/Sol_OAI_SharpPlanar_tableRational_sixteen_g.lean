-- Prove2me | solution 1 for OAI.SharpPlanar.tableRational_sixteen_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:30.257395+00:00
-- url     : https://prove2.me/submissions/f7e71caa-7ddd-4686-9dcd-b0527708b529

import Mathlib
import Definitions.Def_OAIQ098G379

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
lemma tableRational_sixteen_g_oai : tableRational 16 < 15/1000 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableRational_sixteen_g_oai := @OAI.SharpPlanar.tableRational_sixteen_g_oai
