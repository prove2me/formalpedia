-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r1_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:37:32.549308+00:00
-- url     : https://prove2.me/submissions/a2d7c743-c5c8-489d-a64a-bf426c081e68

import Mathlib
import Definitions.Def_OAIQ098G387
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_15_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel1
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
lemma density0_r1_0_eq : ∀ k : Fin 16, density0Expr 1 0 k = density0_r1_0 k := by decide +kernel
lemma density0_r1_eq_g_oai (i k : Fin 16) : density0Expr 1 i k = density0_r1 i k := by
  fin_cases i
  · exact density0_r1_0_eq k
  · exact density0_r1_1_eq_g k
  · exact density0_r1_2_eq_g k
  · exact density0_r1_3_eq_g k
  · exact density0_r1_4_eq_g k
  · exact density0_r1_5_eq_g k
  · exact density0_r1_6_eq_g k
  · exact density0_r1_7_eq_g k
  · exact density0_r1_8_eq_g k
  · exact density0_r1_9_eq_g k
  · exact density0_r1_10_eq_g k
  · exact density0_r1_11_eq_g k
  · exact density0_r1_12_eq_g k
  · exact density0_r1_13_eq_g k
  · exact density0_r1_14_eq_g k
  · exact density0_r1_15_eq_g k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r1_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r1_eq_g_oai
