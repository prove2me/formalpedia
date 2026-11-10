-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm59_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:07:05.129579+00:00
-- url     : https://prove2.me/submissions/fd4a0b0c-df74-4fde-95c1-1fa08d421682

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
lemma tableTerm59_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 59 j i k).Contains (((if d then (tableD a 59:ℝ) else (tableC a 59:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 59 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm59_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm59_contains_g_oai
