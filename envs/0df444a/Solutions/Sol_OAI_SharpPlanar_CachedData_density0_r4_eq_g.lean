-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_r4_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:43:07.267287+00:00
-- url     : https://prove2.me/submissions/6e3e8d58-93e1-4765-a3e1-73f1d779b6b8

import Mathlib
import Definitions.Def_OAIQ098G392
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_15_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_9_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel4
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
lemma density0_r4_0_eq : ∀ k : Fin 16, density0Expr 4 0 k = density0_r4_0 k := by decide +kernel
lemma density0_r4_eq_g_oai (i k : Fin 16) : density0Expr 4 i k = density0_r4 i k := by
  fin_cases i
  · exact density0_r4_0_eq k
  · exact density0_r4_1_eq_g k
  · exact density0_r4_2_eq_g k
  · exact density0_r4_3_eq_g k
  · exact density0_r4_4_eq_g k
  · exact density0_r4_5_eq_g k
  · exact density0_r4_6_eq_g k
  · exact density0_r4_7_eq_g k
  · exact density0_r4_8_eq_g k
  · exact density0_r4_9_eq_g k
  · exact density0_r4_10_eq_g k
  · exact density0_r4_11_eq_g k
  · exact density0_r4_12_eq_g k
  · exact density0_r4_13_eq_g k
  · exact density0_r4_14_eq_g k
  · exact density0_r4_15_eq_g k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_r4_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_r4_eq_g_oai
