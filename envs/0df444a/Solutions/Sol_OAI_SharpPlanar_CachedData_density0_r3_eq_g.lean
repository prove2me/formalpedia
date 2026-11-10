-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r3_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:38:02.890802+00:00
-- url     : https://prove2.me/submissions/de5ea312-5c62-4ba1-9cb4-4c2c6e0cf062

import Mathlib
import Definitions.Def_OAIQ098G389
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel3
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
lemma density0_r3_15_eq : ∀ k : Fin 16, density0Expr 3 15 k = density0_r3_15 k := by decide +kernel
lemma density0_r3_eq_g_oai (i k : Fin 16) : density0Expr 3 i k = density0_r3 i k := by
  fin_cases i
  · exact density0_r3_0_eq_g k
  · exact density0_r3_1_eq_g k
  · exact density0_r3_2_eq_g k
  · exact density0_r3_3_eq_g k
  · exact density0_r3_4_eq_g k
  · exact density0_r3_5_eq_g k
  · exact density0_r3_6_eq_g k
  · exact density0_r3_7_eq_g k
  · exact density0_r3_8_eq_g k
  · exact density0_r3_9_eq_g k
  · exact density0_r3_10_eq_g k
  · exact density0_r3_11_eq_g k
  · exact density0_r3_12_eq_g k
  · exact density0_r3_13_eq_g k
  · exact density0_r3_14_eq_g k
  · exact density0_r3_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r3_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r3_eq_g_oai
