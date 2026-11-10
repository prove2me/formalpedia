-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm23_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:02:23.561205+00:00
-- url     : https://prove2.me/submissions/e94f11a1-ab64-4863-a364-31cf73a4ff1d

import Mathlib
import Definitions.Def_OAIQ098G397

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensityExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma tableTerm23_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 23 j i k).Contains (((if d then (tableD a 23:ℝ) else (tableC a 23:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 23 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm23_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm23_contains_g_oai
