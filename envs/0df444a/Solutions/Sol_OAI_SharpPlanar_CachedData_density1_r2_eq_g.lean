-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density1_r2_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:52:16.021037+00:00
-- url     : https://prove2.me/submissions/8282d5b3-47e1-4be9-b230-2bb1e104884e

import Mathlib
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G403
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_r2_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel2
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
lemma density1_r2_15_eq : ∀ k : Fin 16, density1Expr 2 15 k = density1_r2_15 k := by decide +kernel
lemma density1_r2_eq_g_oai (i k : Fin 16) : density1Expr 2 i k = density1_r2 i k := by
  fin_cases i
  · exact density1_r2_0_eq_g k
  · exact density1_r2_1_eq_g k
  · exact density1_r2_2_eq_g k
  · exact density1_r2_3_eq_g k
  · exact density1_r2_4_eq_g k
  · exact density1_r2_5_eq_g k
  · exact density1_r2_6_eq_g k
  · exact density1_r2_7_eq_g k
  · exact density1_r2_8_eq_g k
  · exact density1_r2_9_eq_g k
  · exact density1_r2_10_eq_g k
  · exact density1_r2_11_eq_g k
  · exact density1_r2_12_eq_g k
  · exact density1_r2_13_eq_g k
  · exact density1_r2_14_eq_g k
  · exact density1_r2_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density1_r2_eq_g_oai := @OAI.SharpPlanar.CachedData.density1_r2_eq_g_oai
