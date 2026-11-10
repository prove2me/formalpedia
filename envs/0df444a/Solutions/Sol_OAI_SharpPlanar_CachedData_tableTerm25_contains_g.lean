-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm25_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:02:27.290933+00:00
-- url     : https://prove2.me/submissions/65d3df67-9da2-48e1-a974-078a45d0802a

import Mathlib
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_column25_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column25_1_contains_g
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
lemma tableTerm25_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 25 j i k).Contains (((if d then (tableD a 25:ℝ) else (tableC a 25:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 25 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis_g (column25_0_contains_g j i k) a
  · exact scaled_table_basis_g (column25_1_contains_g j i k) a
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm25_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm25_contains_g_oai
