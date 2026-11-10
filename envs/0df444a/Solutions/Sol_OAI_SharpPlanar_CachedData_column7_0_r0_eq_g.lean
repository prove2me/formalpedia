-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column7_0_r0_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:38:34.349294+00:00
-- url     : https://prove2.me/submissions/96285f10-e3de-4c78-9f95-2f89799a9fdf

import Mathlib
import Definitions.Def_OAIQ098G210
import Definitions.Def_OAIQ098G288

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
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
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column7_0_r0_0_eq : ∀ k : Fin 16, column7_0Expr 0 0 k = column7_0_r0_0 k := by decide +kernel
lemma column7_0_r0_1_eq : ∀ k : Fin 16, column7_0Expr 0 1 k = column7_0_r0_1 k := by decide +kernel
lemma column7_0_r0_2_eq : ∀ k : Fin 16, column7_0Expr 0 2 k = column7_0_r0_2 k := by decide +kernel
lemma column7_0_r0_3_eq : ∀ k : Fin 16, column7_0Expr 0 3 k = column7_0_r0_3 k := by decide +kernel
lemma column7_0_r0_4_eq : ∀ k : Fin 16, column7_0Expr 0 4 k = column7_0_r0_4 k := by decide +kernel
lemma column7_0_r0_5_eq : ∀ k : Fin 16, column7_0Expr 0 5 k = column7_0_r0_5 k := by decide +kernel
lemma column7_0_r0_6_eq : ∀ k : Fin 16, column7_0Expr 0 6 k = column7_0_r0_6 k := by decide +kernel
lemma column7_0_r0_7_eq : ∀ k : Fin 16, column7_0Expr 0 7 k = column7_0_r0_7 k := by decide +kernel
lemma column7_0_r0_8_eq : ∀ k : Fin 16, column7_0Expr 0 8 k = column7_0_r0_8 k := by decide +kernel
lemma column7_0_r0_9_eq : ∀ k : Fin 16, column7_0Expr 0 9 k = column7_0_r0_9 k := by decide +kernel
lemma column7_0_r0_10_eq : ∀ k : Fin 16, column7_0Expr 0 10 k = column7_0_r0_10 k := by decide +kernel
lemma column7_0_r0_11_eq : ∀ k : Fin 16, column7_0Expr 0 11 k = column7_0_r0_11 k := by decide +kernel
lemma column7_0_r0_12_eq : ∀ k : Fin 16, column7_0Expr 0 12 k = column7_0_r0_12 k := by decide +kernel
lemma column7_0_r0_13_eq : ∀ k : Fin 16, column7_0Expr 0 13 k = column7_0_r0_13 k := by decide +kernel
lemma column7_0_r0_14_eq : ∀ k : Fin 16, column7_0Expr 0 14 k = column7_0_r0_14 k := by decide +kernel
lemma column7_0_r0_15_eq : ∀ k : Fin 16, column7_0Expr 0 15 k = column7_0_r0_15 k := by decide +kernel
lemma column7_0_r0_eq_g_oai (i k : Fin 16) : column7_0Expr 0 i k = column7_0_r0 i k := by
  fin_cases i
  · exact column7_0_r0_0_eq k
  · exact column7_0_r0_1_eq k
  · exact column7_0_r0_2_eq k
  · exact column7_0_r0_3_eq k
  · exact column7_0_r0_4_eq k
  · exact column7_0_r0_5_eq k
  · exact column7_0_r0_6_eq k
  · exact column7_0_r0_7_eq k
  · exact column7_0_r0_8_eq k
  · exact column7_0_r0_9_eq k
  · exact column7_0_r0_10_eq k
  · exact column7_0_r0_11_eq k
  · exact column7_0_r0_12_eq k
  · exact column7_0_r0_13_eq k
  · exact column7_0_r0_14_eq k
  · exact column7_0_r0_15_eq k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column7_0_r0_eq_g_oai := @OAI.SharpPlanar.CachedData.column7_0_r0_eq_g_oai
