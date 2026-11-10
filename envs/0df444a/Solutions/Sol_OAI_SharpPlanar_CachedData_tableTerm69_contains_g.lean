-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm69_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:18:55.868251+00:00
-- url     : https://prove2.me/submissions/0f458e6c-c184-49da-a8c9-380b5e1f6942

import Mathlib
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_column69_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column69_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_scaled_table_basis_g

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
lemma tableTerm69_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 69 j i k).Contains (((if d then (tableD a 69:ℝ) else (tableC a 69:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 69 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis_g (column69_0_contains_g j i k) a
  · exact scaled_table_basis_g (column69_1_contains_g j i k) a
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm69_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm69_contains_g_oai
