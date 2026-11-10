-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r2_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:37:41.722088+00:00
-- url     : https://prove2.me/submissions/61e6833f-a626-4855-b98e-0ee2d09c8df5

import Mathlib
import Definitions.Def_OAIQ098G388
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel2
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
lemma density0_r2_15_eq : ∀ k : Fin 16, density0Expr 2 15 k = density0_r2_15 k := by decide +kernel
lemma density0_r2_eq_g_oai (i k : Fin 16) : density0Expr 2 i k = density0_r2 i k := by
  fin_cases i
  · exact density0_r2_0_eq_g k
  · exact density0_r2_1_eq_g k
  · exact density0_r2_2_eq_g k
  · exact density0_r2_3_eq_g k
  · exact density0_r2_4_eq_g k
  · exact density0_r2_5_eq_g k
  · exact density0_r2_6_eq_g k
  · exact density0_r2_7_eq_g k
  · exact density0_r2_8_eq_g k
  · exact density0_r2_9_eq_g k
  · exact density0_r2_10_eq_g k
  · exact density0_r2_11_eq_g k
  · exact density0_r2_12_eq_g k
  · exact density0_r2_13_eq_g k
  · exact density0_r2_14_eq_g k
  · exact density0_r2_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r2_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r2_eq_g_oai
