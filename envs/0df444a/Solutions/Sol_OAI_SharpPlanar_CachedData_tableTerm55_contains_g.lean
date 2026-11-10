-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm55_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:06:29.282608+00:00
-- url     : https://prove2.me/submissions/ec473bf0-0d42-4fa1-a9a1-b32a140c6497

import Mathlib
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_column55_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column55_1_contains_g
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
lemma tableTerm55_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 55 j i k).Contains (((if d then (tableD a 55:ℝ) else (tableC a 55:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 55 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis_g (column55_0_contains_g j i k) a
  · exact scaled_table_basis_g (column55_1_contains_g j i k) a
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm55_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm55_contains_g_oai
