-- Prove2me | solution 1 for OAI.SharpPlanar.tableRational_hundred_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:28.733198+00:00
-- url     : https://prove2.me/submissions/ed160435-e226-4338-9f4c-ef02adb0ca59

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
lemma tableRational_hundred_g_oai : tableRational 100 < 5/10^10 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableRational_hundred_g_oai := @OAI.SharpPlanar.tableRational_hundred_g_oai
