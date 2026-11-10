-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T18:37:30.800694+00:00
-- url     : https://prove2.me/submissions/164566a6-a0da-4f92-b31f-d74beff1f909

import Mathlib
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_10_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_11_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_12_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_13_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_14_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_5_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_7_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_8_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r0_9_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_r5_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel0
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
lemma density0_r0_15_eq : ∀ k : Fin 16, density0Expr 0 15 k = density0_r0_15 k := by decide +kernel
lemma density0_r0_eq (i k : Fin 16) : density0Expr 0 i k = density0_r0 i k := by
  fin_cases i
  · exact density0_r0_0_eq_g k
  · exact density0_r0_1_eq_g k
  · exact density0_r0_2_eq_g k
  · exact density0_r0_3_eq_g k
  · exact density0_r0_4_eq_g k
  · exact density0_r0_5_eq_g k
  · exact density0_r0_6_eq_g k
  · exact density0_r0_7_eq_g k
  · exact density0_r0_8_eq_g k
  · exact density0_r0_9_eq_g k
  · exact density0_r0_10_eq_g k
  · exact density0_r0_11_eq_g k
  · exact density0_r0_12_eq_g k
  · exact density0_r0_13_eq_g k
  · exact density0_r0_14_eq_g k
  · exact density0_r0_15_eq k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensityValues
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
lemma density0_eq_g_oai (j : Fin 6) (i k : Fin 16) : density0Expr j i k = density0 j i k := by
  fin_cases j
  · exact density0_r0_eq i k
  · exact density0_r1_eq_g i k
  · exact density0_r2_eq_g i k
  · exact density0_r3_eq_g i k
  · exact density0_r4_eq_g i k
  · exact density0_r5_eq_g i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_eq_g_oai := @OAI.SharpPlanar.CachedData.density0_eq_g_oai
