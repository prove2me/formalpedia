-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm7_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:19:02.896545+00:00
-- url     : https://prove2.me/submissions/6f05730d-1a6b-46b5-8358-b6ab113b94f5

import Mathlib
import Definitions.Def_OAIQ098G288
import Definitions.Def_OAIQ098G344
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_amp7_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column7_0_r0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column7_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power7_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisAlpha_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisBeta_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisFunction_wave_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_scaled_table_basis_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod_g,basisBeta_mod_g]

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
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
lemma power7_contains (j : Fin 6) (i k : Fin 16) :
    (power7 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(7:ℕ))) := by
  rw [← power7_eq_g]
  unfold power7Expr
  convert exp_direct_step_g (power6_contains_g j i k) (gridRows_contains_g j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

end OAI
end

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
lemma column7_0_r1_0_eq : ∀ k : Fin 16, column7_0Expr 1 0 k = column7_0_r1_0 k := by decide +kernel
lemma column7_0_r1_1_eq : ∀ k : Fin 16, column7_0Expr 1 1 k = column7_0_r1_1 k := by decide +kernel
lemma column7_0_r1_2_eq : ∀ k : Fin 16, column7_0Expr 1 2 k = column7_0_r1_2 k := by decide +kernel
lemma column7_0_r1_3_eq : ∀ k : Fin 16, column7_0Expr 1 3 k = column7_0_r1_3 k := by decide +kernel
lemma column7_0_r1_4_eq : ∀ k : Fin 16, column7_0Expr 1 4 k = column7_0_r1_4 k := by decide +kernel
lemma column7_0_r1_5_eq : ∀ k : Fin 16, column7_0Expr 1 5 k = column7_0_r1_5 k := by decide +kernel
lemma column7_0_r1_6_eq : ∀ k : Fin 16, column7_0Expr 1 6 k = column7_0_r1_6 k := by decide +kernel
lemma column7_0_r1_7_eq : ∀ k : Fin 16, column7_0Expr 1 7 k = column7_0_r1_7 k := by decide +kernel
lemma column7_0_r1_8_eq : ∀ k : Fin 16, column7_0Expr 1 8 k = column7_0_r1_8 k := by decide +kernel
lemma column7_0_r1_9_eq : ∀ k : Fin 16, column7_0Expr 1 9 k = column7_0_r1_9 k := by decide +kernel
lemma column7_0_r1_10_eq : ∀ k : Fin 16, column7_0Expr 1 10 k = column7_0_r1_10 k := by decide +kernel
lemma column7_0_r1_11_eq : ∀ k : Fin 16, column7_0Expr 1 11 k = column7_0_r1_11 k := by decide +kernel
lemma column7_0_r1_12_eq : ∀ k : Fin 16, column7_0Expr 1 12 k = column7_0_r1_12 k := by decide +kernel
lemma column7_0_r1_13_eq : ∀ k : Fin 16, column7_0Expr 1 13 k = column7_0_r1_13 k := by decide +kernel
lemma column7_0_r1_14_eq : ∀ k : Fin 16, column7_0Expr 1 14 k = column7_0_r1_14 k := by decide +kernel
lemma column7_0_r1_15_eq : ∀ k : Fin 16, column7_0Expr 1 15 k = column7_0_r1_15 k := by decide +kernel
lemma column7_0_r1_eq (i k : Fin 16) : column7_0Expr 1 i k = column7_0_r1 i k := by
  fin_cases i
  · exact column7_0_r1_0_eq k
  · exact column7_0_r1_1_eq k
  · exact column7_0_r1_2_eq k
  · exact column7_0_r1_3_eq k
  · exact column7_0_r1_4_eq k
  · exact column7_0_r1_5_eq k
  · exact column7_0_r1_6_eq k
  · exact column7_0_r1_7_eq k
  · exact column7_0_r1_8_eq k
  · exact column7_0_r1_9_eq k
  · exact column7_0_r1_10_eq k
  · exact column7_0_r1_11_eq k
  · exact column7_0_r1_12_eq k
  · exact column7_0_r1_13_eq k
  · exact column7_0_r1_14_eq k
  · exact column7_0_r1_15_eq k
lemma column7_0_r2_0_eq : ∀ k : Fin 16, column7_0Expr 2 0 k = column7_0_r2_0 k := by decide +kernel
lemma column7_0_r2_1_eq : ∀ k : Fin 16, column7_0Expr 2 1 k = column7_0_r2_1 k := by decide +kernel
lemma column7_0_r2_2_eq : ∀ k : Fin 16, column7_0Expr 2 2 k = column7_0_r2_2 k := by decide +kernel
lemma column7_0_r2_3_eq : ∀ k : Fin 16, column7_0Expr 2 3 k = column7_0_r2_3 k := by decide +kernel
lemma column7_0_r2_4_eq : ∀ k : Fin 16, column7_0Expr 2 4 k = column7_0_r2_4 k := by decide +kernel
lemma column7_0_r2_5_eq : ∀ k : Fin 16, column7_0Expr 2 5 k = column7_0_r2_5 k := by decide +kernel
lemma column7_0_r2_6_eq : ∀ k : Fin 16, column7_0Expr 2 6 k = column7_0_r2_6 k := by decide +kernel
lemma column7_0_r2_7_eq : ∀ k : Fin 16, column7_0Expr 2 7 k = column7_0_r2_7 k := by decide +kernel
lemma column7_0_r2_8_eq : ∀ k : Fin 16, column7_0Expr 2 8 k = column7_0_r2_8 k := by decide +kernel
lemma column7_0_r2_9_eq : ∀ k : Fin 16, column7_0Expr 2 9 k = column7_0_r2_9 k := by decide +kernel
lemma column7_0_r2_10_eq : ∀ k : Fin 16, column7_0Expr 2 10 k = column7_0_r2_10 k := by decide +kernel
lemma column7_0_r2_11_eq : ∀ k : Fin 16, column7_0Expr 2 11 k = column7_0_r2_11 k := by decide +kernel
lemma column7_0_r2_12_eq : ∀ k : Fin 16, column7_0Expr 2 12 k = column7_0_r2_12 k := by decide +kernel
lemma column7_0_r2_13_eq : ∀ k : Fin 16, column7_0Expr 2 13 k = column7_0_r2_13 k := by decide +kernel
lemma column7_0_r2_14_eq : ∀ k : Fin 16, column7_0Expr 2 14 k = column7_0_r2_14 k := by decide +kernel
lemma column7_0_r2_15_eq : ∀ k : Fin 16, column7_0Expr 2 15 k = column7_0_r2_15 k := by decide +kernel
lemma column7_0_r2_eq (i k : Fin 16) : column7_0Expr 2 i k = column7_0_r2 i k := by
  fin_cases i
  · exact column7_0_r2_0_eq k
  · exact column7_0_r2_1_eq k
  · exact column7_0_r2_2_eq k
  · exact column7_0_r2_3_eq k
  · exact column7_0_r2_4_eq k
  · exact column7_0_r2_5_eq k
  · exact column7_0_r2_6_eq k
  · exact column7_0_r2_7_eq k
  · exact column7_0_r2_8_eq k
  · exact column7_0_r2_9_eq k
  · exact column7_0_r2_10_eq k
  · exact column7_0_r2_11_eq k
  · exact column7_0_r2_12_eq k
  · exact column7_0_r2_13_eq k
  · exact column7_0_r2_14_eq k
  · exact column7_0_r2_15_eq k
lemma column7_0_r3_0_eq : ∀ k : Fin 16, column7_0Expr 3 0 k = column7_0_r3_0 k := by decide +kernel
lemma column7_0_r3_1_eq : ∀ k : Fin 16, column7_0Expr 3 1 k = column7_0_r3_1 k := by decide +kernel
lemma column7_0_r3_2_eq : ∀ k : Fin 16, column7_0Expr 3 2 k = column7_0_r3_2 k := by decide +kernel
lemma column7_0_r3_3_eq : ∀ k : Fin 16, column7_0Expr 3 3 k = column7_0_r3_3 k := by decide +kernel
lemma column7_0_r3_4_eq : ∀ k : Fin 16, column7_0Expr 3 4 k = column7_0_r3_4 k := by decide +kernel
lemma column7_0_r3_5_eq : ∀ k : Fin 16, column7_0Expr 3 5 k = column7_0_r3_5 k := by decide +kernel
lemma column7_0_r3_6_eq : ∀ k : Fin 16, column7_0Expr 3 6 k = column7_0_r3_6 k := by decide +kernel
lemma column7_0_r3_7_eq : ∀ k : Fin 16, column7_0Expr 3 7 k = column7_0_r3_7 k := by decide +kernel
lemma column7_0_r3_8_eq : ∀ k : Fin 16, column7_0Expr 3 8 k = column7_0_r3_8 k := by decide +kernel
lemma column7_0_r3_9_eq : ∀ k : Fin 16, column7_0Expr 3 9 k = column7_0_r3_9 k := by decide +kernel
lemma column7_0_r3_10_eq : ∀ k : Fin 16, column7_0Expr 3 10 k = column7_0_r3_10 k := by decide +kernel
lemma column7_0_r3_11_eq : ∀ k : Fin 16, column7_0Expr 3 11 k = column7_0_r3_11 k := by decide +kernel
lemma column7_0_r3_12_eq : ∀ k : Fin 16, column7_0Expr 3 12 k = column7_0_r3_12 k := by decide +kernel
lemma column7_0_r3_13_eq : ∀ k : Fin 16, column7_0Expr 3 13 k = column7_0_r3_13 k := by decide +kernel
lemma column7_0_r3_14_eq : ∀ k : Fin 16, column7_0Expr 3 14 k = column7_0_r3_14 k := by decide +kernel
lemma column7_0_r3_15_eq : ∀ k : Fin 16, column7_0Expr 3 15 k = column7_0_r3_15 k := by decide +kernel
lemma column7_0_r3_eq (i k : Fin 16) : column7_0Expr 3 i k = column7_0_r3 i k := by
  fin_cases i
  · exact column7_0_r3_0_eq k
  · exact column7_0_r3_1_eq k
  · exact column7_0_r3_2_eq k
  · exact column7_0_r3_3_eq k
  · exact column7_0_r3_4_eq k
  · exact column7_0_r3_5_eq k
  · exact column7_0_r3_6_eq k
  · exact column7_0_r3_7_eq k
  · exact column7_0_r3_8_eq k
  · exact column7_0_r3_9_eq k
  · exact column7_0_r3_10_eq k
  · exact column7_0_r3_11_eq k
  · exact column7_0_r3_12_eq k
  · exact column7_0_r3_13_eq k
  · exact column7_0_r3_14_eq k
  · exact column7_0_r3_15_eq k
lemma column7_0_r4_0_eq : ∀ k : Fin 16, column7_0Expr 4 0 k = column7_0_r4_0 k := by decide +kernel
lemma column7_0_r4_1_eq : ∀ k : Fin 16, column7_0Expr 4 1 k = column7_0_r4_1 k := by decide +kernel
lemma column7_0_r4_2_eq : ∀ k : Fin 16, column7_0Expr 4 2 k = column7_0_r4_2 k := by decide +kernel
lemma column7_0_r4_3_eq : ∀ k : Fin 16, column7_0Expr 4 3 k = column7_0_r4_3 k := by decide +kernel
lemma column7_0_r4_4_eq : ∀ k : Fin 16, column7_0Expr 4 4 k = column7_0_r4_4 k := by decide +kernel
lemma column7_0_r4_5_eq : ∀ k : Fin 16, column7_0Expr 4 5 k = column7_0_r4_5 k := by decide +kernel
lemma column7_0_r4_6_eq : ∀ k : Fin 16, column7_0Expr 4 6 k = column7_0_r4_6 k := by decide +kernel
lemma column7_0_r4_7_eq : ∀ k : Fin 16, column7_0Expr 4 7 k = column7_0_r4_7 k := by decide +kernel
lemma column7_0_r4_8_eq : ∀ k : Fin 16, column7_0Expr 4 8 k = column7_0_r4_8 k := by decide +kernel
lemma column7_0_r4_9_eq : ∀ k : Fin 16, column7_0Expr 4 9 k = column7_0_r4_9 k := by decide +kernel
lemma column7_0_r4_10_eq : ∀ k : Fin 16, column7_0Expr 4 10 k = column7_0_r4_10 k := by decide +kernel
lemma column7_0_r4_11_eq : ∀ k : Fin 16, column7_0Expr 4 11 k = column7_0_r4_11 k := by decide +kernel
lemma column7_0_r4_12_eq : ∀ k : Fin 16, column7_0Expr 4 12 k = column7_0_r4_12 k := by decide +kernel
lemma column7_0_r4_13_eq : ∀ k : Fin 16, column7_0Expr 4 13 k = column7_0_r4_13 k := by decide +kernel
lemma column7_0_r4_14_eq : ∀ k : Fin 16, column7_0Expr 4 14 k = column7_0_r4_14 k := by decide +kernel
lemma column7_0_r4_15_eq : ∀ k : Fin 16, column7_0Expr 4 15 k = column7_0_r4_15 k := by decide +kernel
lemma column7_0_r4_eq (i k : Fin 16) : column7_0Expr 4 i k = column7_0_r4 i k := by
  fin_cases i
  · exact column7_0_r4_0_eq k
  · exact column7_0_r4_1_eq k
  · exact column7_0_r4_2_eq k
  · exact column7_0_r4_3_eq k
  · exact column7_0_r4_4_eq k
  · exact column7_0_r4_5_eq k
  · exact column7_0_r4_6_eq k
  · exact column7_0_r4_7_eq k
  · exact column7_0_r4_8_eq k
  · exact column7_0_r4_9_eq k
  · exact column7_0_r4_10_eq k
  · exact column7_0_r4_11_eq k
  · exact column7_0_r4_12_eq k
  · exact column7_0_r4_13_eq k
  · exact column7_0_r4_14_eq k
  · exact column7_0_r4_15_eq k
lemma column7_0_r5_0_eq : ∀ k : Fin 16, column7_0Expr 5 0 k = column7_0_r5_0 k := by decide +kernel
lemma column7_0_r5_1_eq : ∀ k : Fin 16, column7_0Expr 5 1 k = column7_0_r5_1 k := by decide +kernel
lemma column7_0_r5_2_eq : ∀ k : Fin 16, column7_0Expr 5 2 k = column7_0_r5_2 k := by decide +kernel
lemma column7_0_r5_3_eq : ∀ k : Fin 16, column7_0Expr 5 3 k = column7_0_r5_3 k := by decide +kernel
lemma column7_0_r5_4_eq : ∀ k : Fin 16, column7_0Expr 5 4 k = column7_0_r5_4 k := by decide +kernel
lemma column7_0_r5_5_eq : ∀ k : Fin 16, column7_0Expr 5 5 k = column7_0_r5_5 k := by decide +kernel
lemma column7_0_r5_6_eq : ∀ k : Fin 16, column7_0Expr 5 6 k = column7_0_r5_6 k := by decide +kernel
lemma column7_0_r5_7_eq : ∀ k : Fin 16, column7_0Expr 5 7 k = column7_0_r5_7 k := by decide +kernel
lemma column7_0_r5_8_eq : ∀ k : Fin 16, column7_0Expr 5 8 k = column7_0_r5_8 k := by decide +kernel
lemma column7_0_r5_9_eq : ∀ k : Fin 16, column7_0Expr 5 9 k = column7_0_r5_9 k := by decide +kernel
lemma column7_0_r5_10_eq : ∀ k : Fin 16, column7_0Expr 5 10 k = column7_0_r5_10 k := by decide +kernel
lemma column7_0_r5_11_eq : ∀ k : Fin 16, column7_0Expr 5 11 k = column7_0_r5_11 k := by decide +kernel
lemma column7_0_r5_12_eq : ∀ k : Fin 16, column7_0Expr 5 12 k = column7_0_r5_12 k := by decide +kernel
lemma column7_0_r5_13_eq : ∀ k : Fin 16, column7_0Expr 5 13 k = column7_0_r5_13 k := by decide +kernel
lemma column7_0_r5_14_eq : ∀ k : Fin 16, column7_0Expr 5 14 k = column7_0_r5_14 k := by decide +kernel
lemma column7_0_r5_15_eq : ∀ k : Fin 16, column7_0Expr 5 15 k = column7_0_r5_15 k := by decide +kernel
lemma column7_0_r5_eq (i k : Fin 16) : column7_0Expr 5 i k = column7_0_r5 i k := by
  fin_cases i
  · exact column7_0_r5_0_eq k
  · exact column7_0_r5_1_eq k
  · exact column7_0_r5_2_eq k
  · exact column7_0_r5_3_eq k
  · exact column7_0_r5_4_eq k
  · exact column7_0_r5_5_eq k
  · exact column7_0_r5_6_eq k
  · exact column7_0_r5_7_eq k
  · exact column7_0_r5_8_eq k
  · exact column7_0_r5_9_eq k
  · exact column7_0_r5_10_eq k
  · exact column7_0_r5_11_eq k
  · exact column7_0_r5_12_eq k
  · exact column7_0_r5_13_eq k
  · exact column7_0_r5_14_eq k
  · exact column7_0_r5_15_eq k
lemma column7_0_eq (j : Fin 6) (i k : Fin 16) : column7_0Expr j i k = column7_0 j i k := by
  fin_cases j
  · exact column7_0_r0_eq_g i k
  · exact column7_0_r1_eq i k
  · exact column7_0_r2_eq i k
  · exact column7_0_r3_eq i k
  · exact column7_0_r4_eq i k
  · exact column7_0_r5_eq i k
lemma column7_0_contains (j : Fin 6) (i k : Fin 16) :
    (column7_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 7 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column7_0_eq,basisFunction_wave_g,← mul_assoc]
  unfold column7_0Expr
  apply CBox.contains_mul_g
  · rw [← waveAmplitude_mod false 7 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp7_0_contains_g j i k
  · exact power7_contains j i k
end SharpPlanar.CachedData

end OAI
end

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
lemma tableTerm7_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 7 j i k).Contains (((if d then (tableD a 7:ℝ) else (tableC a 7:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 7 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis_g (column7_0_contains j i k) a
  · exact scaled_table_basis_g (column7_1_contains_g j i k) a
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm7_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm7_contains_g_oai
