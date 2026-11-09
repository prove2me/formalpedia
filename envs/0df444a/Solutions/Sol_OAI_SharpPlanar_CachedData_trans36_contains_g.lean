-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.trans36_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:03:12.765754+00:00
-- url     : https://prove2.me/submissions/d589f3f3-042d-42bb-8eb1-990361a395f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1605
import Definitions.Def_OAIQ098G1607
import Definitions.Def_OAIQ098G1610
import Theorems.Thm_OAI_SharpPlanar_CachedData_trans32_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_transformed_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (Complex.I*Real.pi*z t*n)))
    (hq : q.Contains (Complex.exp (Complex.I*Real.pi*z t))) :
    (p.mul q).Contains (Complex.exp (Complex.I*Real.pi*z t*(n+1))) := by
  have hh := CBox.contains_mul_g hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers40
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
lemma trans33_r0_0_eq : ∀ k : Fin 16, trans33Expr 0 0 k = trans33_r0_0 k := by decide +kernel
lemma trans33_r0_1_eq : ∀ k : Fin 16, trans33Expr 0 1 k = trans33_r0_1 k := by decide +kernel
lemma trans33_r0_2_eq : ∀ k : Fin 16, trans33Expr 0 2 k = trans33_r0_2 k := by decide +kernel
lemma trans33_r0_3_eq : ∀ k : Fin 16, trans33Expr 0 3 k = trans33_r0_3 k := by decide +kernel
lemma trans33_r0_4_eq : ∀ k : Fin 16, trans33Expr 0 4 k = trans33_r0_4 k := by decide +kernel
lemma trans33_r0_5_eq : ∀ k : Fin 16, trans33Expr 0 5 k = trans33_r0_5 k := by decide +kernel
lemma trans33_r0_6_eq : ∀ k : Fin 16, trans33Expr 0 6 k = trans33_r0_6 k := by decide +kernel
lemma trans33_r0_7_eq : ∀ k : Fin 16, trans33Expr 0 7 k = trans33_r0_7 k := by decide +kernel
lemma trans33_r0_8_eq : ∀ k : Fin 16, trans33Expr 0 8 k = trans33_r0_8 k := by decide +kernel
lemma trans33_r0_9_eq : ∀ k : Fin 16, trans33Expr 0 9 k = trans33_r0_9 k := by decide +kernel
lemma trans33_r0_10_eq : ∀ k : Fin 16, trans33Expr 0 10 k = trans33_r0_10 k := by decide +kernel
lemma trans33_r0_11_eq : ∀ k : Fin 16, trans33Expr 0 11 k = trans33_r0_11 k := by decide +kernel
lemma trans33_r0_12_eq : ∀ k : Fin 16, trans33Expr 0 12 k = trans33_r0_12 k := by decide +kernel
lemma trans33_r0_13_eq : ∀ k : Fin 16, trans33Expr 0 13 k = trans33_r0_13 k := by decide +kernel
lemma trans33_r0_14_eq : ∀ k : Fin 16, trans33Expr 0 14 k = trans33_r0_14 k := by decide +kernel
lemma trans33_r0_15_eq : ∀ k : Fin 16, trans33Expr 0 15 k = trans33_r0_15 k := by decide +kernel
lemma trans33_r0_eq (i k : Fin 16) : trans33Expr 0 i k = trans33_r0 i k := by
  fin_cases i
  · exact trans33_r0_0_eq k
  · exact trans33_r0_1_eq k
  · exact trans33_r0_2_eq k
  · exact trans33_r0_3_eq k
  · exact trans33_r0_4_eq k
  · exact trans33_r0_5_eq k
  · exact trans33_r0_6_eq k
  · exact trans33_r0_7_eq k
  · exact trans33_r0_8_eq k
  · exact trans33_r0_9_eq k
  · exact trans33_r0_10_eq k
  · exact trans33_r0_11_eq k
  · exact trans33_r0_12_eq k
  · exact trans33_r0_13_eq k
  · exact trans33_r0_14_eq k
  · exact trans33_r0_15_eq k
lemma trans33_r1_0_eq : ∀ k : Fin 16, trans33Expr 1 0 k = trans33_r1_0 k := by decide +kernel
lemma trans33_r1_1_eq : ∀ k : Fin 16, trans33Expr 1 1 k = trans33_r1_1 k := by decide +kernel
lemma trans33_r1_2_eq : ∀ k : Fin 16, trans33Expr 1 2 k = trans33_r1_2 k := by decide +kernel
lemma trans33_r1_3_eq : ∀ k : Fin 16, trans33Expr 1 3 k = trans33_r1_3 k := by decide +kernel
lemma trans33_r1_4_eq : ∀ k : Fin 16, trans33Expr 1 4 k = trans33_r1_4 k := by decide +kernel
lemma trans33_r1_5_eq : ∀ k : Fin 16, trans33Expr 1 5 k = trans33_r1_5 k := by decide +kernel
lemma trans33_r1_6_eq : ∀ k : Fin 16, trans33Expr 1 6 k = trans33_r1_6 k := by decide +kernel
lemma trans33_r1_7_eq : ∀ k : Fin 16, trans33Expr 1 7 k = trans33_r1_7 k := by decide +kernel
lemma trans33_r1_8_eq : ∀ k : Fin 16, trans33Expr 1 8 k = trans33_r1_8 k := by decide +kernel
lemma trans33_r1_9_eq : ∀ k : Fin 16, trans33Expr 1 9 k = trans33_r1_9 k := by decide +kernel
lemma trans33_r1_10_eq : ∀ k : Fin 16, trans33Expr 1 10 k = trans33_r1_10 k := by decide +kernel
lemma trans33_r1_11_eq : ∀ k : Fin 16, trans33Expr 1 11 k = trans33_r1_11 k := by decide +kernel
lemma trans33_r1_12_eq : ∀ k : Fin 16, trans33Expr 1 12 k = trans33_r1_12 k := by decide +kernel
lemma trans33_r1_13_eq : ∀ k : Fin 16, trans33Expr 1 13 k = trans33_r1_13 k := by decide +kernel
lemma trans33_r1_14_eq : ∀ k : Fin 16, trans33Expr 1 14 k = trans33_r1_14 k := by decide +kernel
lemma trans33_r1_15_eq : ∀ k : Fin 16, trans33Expr 1 15 k = trans33_r1_15 k := by decide +kernel
lemma trans33_r1_eq (i k : Fin 16) : trans33Expr 1 i k = trans33_r1 i k := by
  fin_cases i
  · exact trans33_r1_0_eq k
  · exact trans33_r1_1_eq k
  · exact trans33_r1_2_eq k
  · exact trans33_r1_3_eq k
  · exact trans33_r1_4_eq k
  · exact trans33_r1_5_eq k
  · exact trans33_r1_6_eq k
  · exact trans33_r1_7_eq k
  · exact trans33_r1_8_eq k
  · exact trans33_r1_9_eq k
  · exact trans33_r1_10_eq k
  · exact trans33_r1_11_eq k
  · exact trans33_r1_12_eq k
  · exact trans33_r1_13_eq k
  · exact trans33_r1_14_eq k
  · exact trans33_r1_15_eq k
lemma trans33_r2_0_eq : ∀ k : Fin 16, trans33Expr 2 0 k = trans33_r2_0 k := by decide +kernel
lemma trans33_r2_1_eq : ∀ k : Fin 16, trans33Expr 2 1 k = trans33_r2_1 k := by decide +kernel
lemma trans33_r2_2_eq : ∀ k : Fin 16, trans33Expr 2 2 k = trans33_r2_2 k := by decide +kernel
lemma trans33_r2_3_eq : ∀ k : Fin 16, trans33Expr 2 3 k = trans33_r2_3 k := by decide +kernel
lemma trans33_r2_4_eq : ∀ k : Fin 16, trans33Expr 2 4 k = trans33_r2_4 k := by decide +kernel
lemma trans33_r2_5_eq : ∀ k : Fin 16, trans33Expr 2 5 k = trans33_r2_5 k := by decide +kernel
lemma trans33_r2_6_eq : ∀ k : Fin 16, trans33Expr 2 6 k = trans33_r2_6 k := by decide +kernel
lemma trans33_r2_7_eq : ∀ k : Fin 16, trans33Expr 2 7 k = trans33_r2_7 k := by decide +kernel
lemma trans33_r2_8_eq : ∀ k : Fin 16, trans33Expr 2 8 k = trans33_r2_8 k := by decide +kernel
lemma trans33_r2_9_eq : ∀ k : Fin 16, trans33Expr 2 9 k = trans33_r2_9 k := by decide +kernel
lemma trans33_r2_10_eq : ∀ k : Fin 16, trans33Expr 2 10 k = trans33_r2_10 k := by decide +kernel
lemma trans33_r2_11_eq : ∀ k : Fin 16, trans33Expr 2 11 k = trans33_r2_11 k := by decide +kernel
lemma trans33_r2_12_eq : ∀ k : Fin 16, trans33Expr 2 12 k = trans33_r2_12 k := by decide +kernel
lemma trans33_r2_13_eq : ∀ k : Fin 16, trans33Expr 2 13 k = trans33_r2_13 k := by decide +kernel
lemma trans33_r2_14_eq : ∀ k : Fin 16, trans33Expr 2 14 k = trans33_r2_14 k := by decide +kernel
lemma trans33_r2_15_eq : ∀ k : Fin 16, trans33Expr 2 15 k = trans33_r2_15 k := by decide +kernel
lemma trans33_r2_eq (i k : Fin 16) : trans33Expr 2 i k = trans33_r2 i k := by
  fin_cases i
  · exact trans33_r2_0_eq k
  · exact trans33_r2_1_eq k
  · exact trans33_r2_2_eq k
  · exact trans33_r2_3_eq k
  · exact trans33_r2_4_eq k
  · exact trans33_r2_5_eq k
  · exact trans33_r2_6_eq k
  · exact trans33_r2_7_eq k
  · exact trans33_r2_8_eq k
  · exact trans33_r2_9_eq k
  · exact trans33_r2_10_eq k
  · exact trans33_r2_11_eq k
  · exact trans33_r2_12_eq k
  · exact trans33_r2_13_eq k
  · exact trans33_r2_14_eq k
  · exact trans33_r2_15_eq k
lemma trans33_r3_0_eq : ∀ k : Fin 16, trans33Expr 3 0 k = trans33_r3_0 k := by decide +kernel
lemma trans33_r3_1_eq : ∀ k : Fin 16, trans33Expr 3 1 k = trans33_r3_1 k := by decide +kernel
lemma trans33_r3_2_eq : ∀ k : Fin 16, trans33Expr 3 2 k = trans33_r3_2 k := by decide +kernel
lemma trans33_r3_3_eq : ∀ k : Fin 16, trans33Expr 3 3 k = trans33_r3_3 k := by decide +kernel
lemma trans33_r3_4_eq : ∀ k : Fin 16, trans33Expr 3 4 k = trans33_r3_4 k := by decide +kernel
lemma trans33_r3_5_eq : ∀ k : Fin 16, trans33Expr 3 5 k = trans33_r3_5 k := by decide +kernel
lemma trans33_r3_6_eq : ∀ k : Fin 16, trans33Expr 3 6 k = trans33_r3_6 k := by decide +kernel
lemma trans33_r3_7_eq : ∀ k : Fin 16, trans33Expr 3 7 k = trans33_r3_7 k := by decide +kernel
lemma trans33_r3_8_eq : ∀ k : Fin 16, trans33Expr 3 8 k = trans33_r3_8 k := by decide +kernel
lemma trans33_r3_9_eq : ∀ k : Fin 16, trans33Expr 3 9 k = trans33_r3_9 k := by decide +kernel
lemma trans33_r3_10_eq : ∀ k : Fin 16, trans33Expr 3 10 k = trans33_r3_10 k := by decide +kernel
lemma trans33_r3_11_eq : ∀ k : Fin 16, trans33Expr 3 11 k = trans33_r3_11 k := by decide +kernel
lemma trans33_r3_12_eq : ∀ k : Fin 16, trans33Expr 3 12 k = trans33_r3_12 k := by decide +kernel
lemma trans33_r3_13_eq : ∀ k : Fin 16, trans33Expr 3 13 k = trans33_r3_13 k := by decide +kernel
lemma trans33_r3_14_eq : ∀ k : Fin 16, trans33Expr 3 14 k = trans33_r3_14 k := by decide +kernel
lemma trans33_r3_15_eq : ∀ k : Fin 16, trans33Expr 3 15 k = trans33_r3_15 k := by decide +kernel
lemma trans33_r3_eq (i k : Fin 16) : trans33Expr 3 i k = trans33_r3 i k := by
  fin_cases i
  · exact trans33_r3_0_eq k
  · exact trans33_r3_1_eq k
  · exact trans33_r3_2_eq k
  · exact trans33_r3_3_eq k
  · exact trans33_r3_4_eq k
  · exact trans33_r3_5_eq k
  · exact trans33_r3_6_eq k
  · exact trans33_r3_7_eq k
  · exact trans33_r3_8_eq k
  · exact trans33_r3_9_eq k
  · exact trans33_r3_10_eq k
  · exact trans33_r3_11_eq k
  · exact trans33_r3_12_eq k
  · exact trans33_r3_13_eq k
  · exact trans33_r3_14_eq k
  · exact trans33_r3_15_eq k
lemma trans33_r4_0_eq : ∀ k : Fin 16, trans33Expr 4 0 k = trans33_r4_0 k := by decide +kernel
lemma trans33_r4_1_eq : ∀ k : Fin 16, trans33Expr 4 1 k = trans33_r4_1 k := by decide +kernel
lemma trans33_r4_2_eq : ∀ k : Fin 16, trans33Expr 4 2 k = trans33_r4_2 k := by decide +kernel
lemma trans33_r4_3_eq : ∀ k : Fin 16, trans33Expr 4 3 k = trans33_r4_3 k := by decide +kernel
lemma trans33_r4_4_eq : ∀ k : Fin 16, trans33Expr 4 4 k = trans33_r4_4 k := by decide +kernel
lemma trans33_r4_5_eq : ∀ k : Fin 16, trans33Expr 4 5 k = trans33_r4_5 k := by decide +kernel
lemma trans33_r4_6_eq : ∀ k : Fin 16, trans33Expr 4 6 k = trans33_r4_6 k := by decide +kernel
lemma trans33_r4_7_eq : ∀ k : Fin 16, trans33Expr 4 7 k = trans33_r4_7 k := by decide +kernel
lemma trans33_r4_8_eq : ∀ k : Fin 16, trans33Expr 4 8 k = trans33_r4_8 k := by decide +kernel
lemma trans33_r4_9_eq : ∀ k : Fin 16, trans33Expr 4 9 k = trans33_r4_9 k := by decide +kernel
lemma trans33_r4_10_eq : ∀ k : Fin 16, trans33Expr 4 10 k = trans33_r4_10 k := by decide +kernel
lemma trans33_r4_11_eq : ∀ k : Fin 16, trans33Expr 4 11 k = trans33_r4_11 k := by decide +kernel
lemma trans33_r4_12_eq : ∀ k : Fin 16, trans33Expr 4 12 k = trans33_r4_12 k := by decide +kernel
lemma trans33_r4_13_eq : ∀ k : Fin 16, trans33Expr 4 13 k = trans33_r4_13 k := by decide +kernel
lemma trans33_r4_14_eq : ∀ k : Fin 16, trans33Expr 4 14 k = trans33_r4_14 k := by decide +kernel
lemma trans33_r4_15_eq : ∀ k : Fin 16, trans33Expr 4 15 k = trans33_r4_15 k := by decide +kernel
lemma trans33_r4_eq (i k : Fin 16) : trans33Expr 4 i k = trans33_r4 i k := by
  fin_cases i
  · exact trans33_r4_0_eq k
  · exact trans33_r4_1_eq k
  · exact trans33_r4_2_eq k
  · exact trans33_r4_3_eq k
  · exact trans33_r4_4_eq k
  · exact trans33_r4_5_eq k
  · exact trans33_r4_6_eq k
  · exact trans33_r4_7_eq k
  · exact trans33_r4_8_eq k
  · exact trans33_r4_9_eq k
  · exact trans33_r4_10_eq k
  · exact trans33_r4_11_eq k
  · exact trans33_r4_12_eq k
  · exact trans33_r4_13_eq k
  · exact trans33_r4_14_eq k
  · exact trans33_r4_15_eq k
lemma trans33_r5_0_eq : ∀ k : Fin 16, trans33Expr 5 0 k = trans33_r5_0 k := by decide +kernel
lemma trans33_r5_1_eq : ∀ k : Fin 16, trans33Expr 5 1 k = trans33_r5_1 k := by decide +kernel
lemma trans33_r5_2_eq : ∀ k : Fin 16, trans33Expr 5 2 k = trans33_r5_2 k := by decide +kernel
lemma trans33_r5_3_eq : ∀ k : Fin 16, trans33Expr 5 3 k = trans33_r5_3 k := by decide +kernel
lemma trans33_r5_4_eq : ∀ k : Fin 16, trans33Expr 5 4 k = trans33_r5_4 k := by decide +kernel
lemma trans33_r5_5_eq : ∀ k : Fin 16, trans33Expr 5 5 k = trans33_r5_5 k := by decide +kernel
lemma trans33_r5_6_eq : ∀ k : Fin 16, trans33Expr 5 6 k = trans33_r5_6 k := by decide +kernel
lemma trans33_r5_7_eq : ∀ k : Fin 16, trans33Expr 5 7 k = trans33_r5_7 k := by decide +kernel
lemma trans33_r5_8_eq : ∀ k : Fin 16, trans33Expr 5 8 k = trans33_r5_8 k := by decide +kernel
lemma trans33_r5_9_eq : ∀ k : Fin 16, trans33Expr 5 9 k = trans33_r5_9 k := by decide +kernel
lemma trans33_r5_10_eq : ∀ k : Fin 16, trans33Expr 5 10 k = trans33_r5_10 k := by decide +kernel
lemma trans33_r5_11_eq : ∀ k : Fin 16, trans33Expr 5 11 k = trans33_r5_11 k := by decide +kernel
lemma trans33_r5_12_eq : ∀ k : Fin 16, trans33Expr 5 12 k = trans33_r5_12 k := by decide +kernel
lemma trans33_r5_13_eq : ∀ k : Fin 16, trans33Expr 5 13 k = trans33_r5_13 k := by decide +kernel
lemma trans33_r5_14_eq : ∀ k : Fin 16, trans33Expr 5 14 k = trans33_r5_14 k := by decide +kernel
lemma trans33_r5_15_eq : ∀ k : Fin 16, trans33Expr 5 15 k = trans33_r5_15 k := by decide +kernel
lemma trans33_r5_eq (i k : Fin 16) : trans33Expr 5 i k = trans33_r5 i k := by
  fin_cases i
  · exact trans33_r5_0_eq k
  · exact trans33_r5_1_eq k
  · exact trans33_r5_2_eq k
  · exact trans33_r5_3_eq k
  · exact trans33_r5_4_eq k
  · exact trans33_r5_5_eq k
  · exact trans33_r5_6_eq k
  · exact trans33_r5_7_eq k
  · exact trans33_r5_8_eq k
  · exact trans33_r5_9_eq k
  · exact trans33_r5_10_eq k
  · exact trans33_r5_11_eq k
  · exact trans33_r5_12_eq k
  · exact trans33_r5_13_eq k
  · exact trans33_r5_14_eq k
  · exact trans33_r5_15_eq k
lemma trans33_eq (j : Fin 6) (i k : Fin 16) : trans33Expr j i k = trans33 j i k := by
  fin_cases j
  · exact trans33_r0_eq i k
  · exact trans33_r1_eq i k
  · exact trans33_r2_eq i k
  · exact trans33_r3_eq i k
  · exact trans33_r4_eq i k
  · exact trans33_r5_eq i k
lemma trans33_contains (j : Fin 6) (i k : Fin 16) :
    (trans33 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(33:ℕ))) := by
  rw [← trans33_eq]
  unfold trans33Expr
  convert exp_transformed_step (trans32_contains_g j i k) (transStep_contains_g j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
lemma trans34_r0_0_eq : ∀ k : Fin 16, trans34Expr 0 0 k = trans34_r0_0 k := by decide +kernel
lemma trans34_r0_1_eq : ∀ k : Fin 16, trans34Expr 0 1 k = trans34_r0_1 k := by decide +kernel
lemma trans34_r0_2_eq : ∀ k : Fin 16, trans34Expr 0 2 k = trans34_r0_2 k := by decide +kernel
lemma trans34_r0_3_eq : ∀ k : Fin 16, trans34Expr 0 3 k = trans34_r0_3 k := by decide +kernel
lemma trans34_r0_4_eq : ∀ k : Fin 16, trans34Expr 0 4 k = trans34_r0_4 k := by decide +kernel
lemma trans34_r0_5_eq : ∀ k : Fin 16, trans34Expr 0 5 k = trans34_r0_5 k := by decide +kernel
lemma trans34_r0_6_eq : ∀ k : Fin 16, trans34Expr 0 6 k = trans34_r0_6 k := by decide +kernel
lemma trans34_r0_7_eq : ∀ k : Fin 16, trans34Expr 0 7 k = trans34_r0_7 k := by decide +kernel
lemma trans34_r0_8_eq : ∀ k : Fin 16, trans34Expr 0 8 k = trans34_r0_8 k := by decide +kernel
lemma trans34_r0_9_eq : ∀ k : Fin 16, trans34Expr 0 9 k = trans34_r0_9 k := by decide +kernel
lemma trans34_r0_10_eq : ∀ k : Fin 16, trans34Expr 0 10 k = trans34_r0_10 k := by decide +kernel
lemma trans34_r0_11_eq : ∀ k : Fin 16, trans34Expr 0 11 k = trans34_r0_11 k := by decide +kernel
lemma trans34_r0_12_eq : ∀ k : Fin 16, trans34Expr 0 12 k = trans34_r0_12 k := by decide +kernel
lemma trans34_r0_13_eq : ∀ k : Fin 16, trans34Expr 0 13 k = trans34_r0_13 k := by decide +kernel
lemma trans34_r0_14_eq : ∀ k : Fin 16, trans34Expr 0 14 k = trans34_r0_14 k := by decide +kernel
lemma trans34_r0_15_eq : ∀ k : Fin 16, trans34Expr 0 15 k = trans34_r0_15 k := by decide +kernel
lemma trans34_r0_eq (i k : Fin 16) : trans34Expr 0 i k = trans34_r0 i k := by
  fin_cases i
  · exact trans34_r0_0_eq k
  · exact trans34_r0_1_eq k
  · exact trans34_r0_2_eq k
  · exact trans34_r0_3_eq k
  · exact trans34_r0_4_eq k
  · exact trans34_r0_5_eq k
  · exact trans34_r0_6_eq k
  · exact trans34_r0_7_eq k
  · exact trans34_r0_8_eq k
  · exact trans34_r0_9_eq k
  · exact trans34_r0_10_eq k
  · exact trans34_r0_11_eq k
  · exact trans34_r0_12_eq k
  · exact trans34_r0_13_eq k
  · exact trans34_r0_14_eq k
  · exact trans34_r0_15_eq k
lemma trans34_r1_0_eq : ∀ k : Fin 16, trans34Expr 1 0 k = trans34_r1_0 k := by decide +kernel
lemma trans34_r1_1_eq : ∀ k : Fin 16, trans34Expr 1 1 k = trans34_r1_1 k := by decide +kernel
lemma trans34_r1_2_eq : ∀ k : Fin 16, trans34Expr 1 2 k = trans34_r1_2 k := by decide +kernel
lemma trans34_r1_3_eq : ∀ k : Fin 16, trans34Expr 1 3 k = trans34_r1_3 k := by decide +kernel
lemma trans34_r1_4_eq : ∀ k : Fin 16, trans34Expr 1 4 k = trans34_r1_4 k := by decide +kernel
lemma trans34_r1_5_eq : ∀ k : Fin 16, trans34Expr 1 5 k = trans34_r1_5 k := by decide +kernel
lemma trans34_r1_6_eq : ∀ k : Fin 16, trans34Expr 1 6 k = trans34_r1_6 k := by decide +kernel
lemma trans34_r1_7_eq : ∀ k : Fin 16, trans34Expr 1 7 k = trans34_r1_7 k := by decide +kernel
lemma trans34_r1_8_eq : ∀ k : Fin 16, trans34Expr 1 8 k = trans34_r1_8 k := by decide +kernel
lemma trans34_r1_9_eq : ∀ k : Fin 16, trans34Expr 1 9 k = trans34_r1_9 k := by decide +kernel
lemma trans34_r1_10_eq : ∀ k : Fin 16, trans34Expr 1 10 k = trans34_r1_10 k := by decide +kernel
lemma trans34_r1_11_eq : ∀ k : Fin 16, trans34Expr 1 11 k = trans34_r1_11 k := by decide +kernel
lemma trans34_r1_12_eq : ∀ k : Fin 16, trans34Expr 1 12 k = trans34_r1_12 k := by decide +kernel
lemma trans34_r1_13_eq : ∀ k : Fin 16, trans34Expr 1 13 k = trans34_r1_13 k := by decide +kernel
lemma trans34_r1_14_eq : ∀ k : Fin 16, trans34Expr 1 14 k = trans34_r1_14 k := by decide +kernel
lemma trans34_r1_15_eq : ∀ k : Fin 16, trans34Expr 1 15 k = trans34_r1_15 k := by decide +kernel
lemma trans34_r1_eq (i k : Fin 16) : trans34Expr 1 i k = trans34_r1 i k := by
  fin_cases i
  · exact trans34_r1_0_eq k
  · exact trans34_r1_1_eq k
  · exact trans34_r1_2_eq k
  · exact trans34_r1_3_eq k
  · exact trans34_r1_4_eq k
  · exact trans34_r1_5_eq k
  · exact trans34_r1_6_eq k
  · exact trans34_r1_7_eq k
  · exact trans34_r1_8_eq k
  · exact trans34_r1_9_eq k
  · exact trans34_r1_10_eq k
  · exact trans34_r1_11_eq k
  · exact trans34_r1_12_eq k
  · exact trans34_r1_13_eq k
  · exact trans34_r1_14_eq k
  · exact trans34_r1_15_eq k
lemma trans34_r2_0_eq : ∀ k : Fin 16, trans34Expr 2 0 k = trans34_r2_0 k := by decide +kernel
lemma trans34_r2_1_eq : ∀ k : Fin 16, trans34Expr 2 1 k = trans34_r2_1 k := by decide +kernel
lemma trans34_r2_2_eq : ∀ k : Fin 16, trans34Expr 2 2 k = trans34_r2_2 k := by decide +kernel
lemma trans34_r2_3_eq : ∀ k : Fin 16, trans34Expr 2 3 k = trans34_r2_3 k := by decide +kernel
lemma trans34_r2_4_eq : ∀ k : Fin 16, trans34Expr 2 4 k = trans34_r2_4 k := by decide +kernel
lemma trans34_r2_5_eq : ∀ k : Fin 16, trans34Expr 2 5 k = trans34_r2_5 k := by decide +kernel
lemma trans34_r2_6_eq : ∀ k : Fin 16, trans34Expr 2 6 k = trans34_r2_6 k := by decide +kernel
lemma trans34_r2_7_eq : ∀ k : Fin 16, trans34Expr 2 7 k = trans34_r2_7 k := by decide +kernel
lemma trans34_r2_8_eq : ∀ k : Fin 16, trans34Expr 2 8 k = trans34_r2_8 k := by decide +kernel
lemma trans34_r2_9_eq : ∀ k : Fin 16, trans34Expr 2 9 k = trans34_r2_9 k := by decide +kernel
lemma trans34_r2_10_eq : ∀ k : Fin 16, trans34Expr 2 10 k = trans34_r2_10 k := by decide +kernel
lemma trans34_r2_11_eq : ∀ k : Fin 16, trans34Expr 2 11 k = trans34_r2_11 k := by decide +kernel
lemma trans34_r2_12_eq : ∀ k : Fin 16, trans34Expr 2 12 k = trans34_r2_12 k := by decide +kernel
lemma trans34_r2_13_eq : ∀ k : Fin 16, trans34Expr 2 13 k = trans34_r2_13 k := by decide +kernel
lemma trans34_r2_14_eq : ∀ k : Fin 16, trans34Expr 2 14 k = trans34_r2_14 k := by decide +kernel
lemma trans34_r2_15_eq : ∀ k : Fin 16, trans34Expr 2 15 k = trans34_r2_15 k := by decide +kernel
lemma trans34_r2_eq (i k : Fin 16) : trans34Expr 2 i k = trans34_r2 i k := by
  fin_cases i
  · exact trans34_r2_0_eq k
  · exact trans34_r2_1_eq k
  · exact trans34_r2_2_eq k
  · exact trans34_r2_3_eq k
  · exact trans34_r2_4_eq k
  · exact trans34_r2_5_eq k
  · exact trans34_r2_6_eq k
  · exact trans34_r2_7_eq k
  · exact trans34_r2_8_eq k
  · exact trans34_r2_9_eq k
  · exact trans34_r2_10_eq k
  · exact trans34_r2_11_eq k
  · exact trans34_r2_12_eq k
  · exact trans34_r2_13_eq k
  · exact trans34_r2_14_eq k
  · exact trans34_r2_15_eq k
lemma trans34_r3_0_eq : ∀ k : Fin 16, trans34Expr 3 0 k = trans34_r3_0 k := by decide +kernel
lemma trans34_r3_1_eq : ∀ k : Fin 16, trans34Expr 3 1 k = trans34_r3_1 k := by decide +kernel
lemma trans34_r3_2_eq : ∀ k : Fin 16, trans34Expr 3 2 k = trans34_r3_2 k := by decide +kernel
lemma trans34_r3_3_eq : ∀ k : Fin 16, trans34Expr 3 3 k = trans34_r3_3 k := by decide +kernel
lemma trans34_r3_4_eq : ∀ k : Fin 16, trans34Expr 3 4 k = trans34_r3_4 k := by decide +kernel
lemma trans34_r3_5_eq : ∀ k : Fin 16, trans34Expr 3 5 k = trans34_r3_5 k := by decide +kernel
lemma trans34_r3_6_eq : ∀ k : Fin 16, trans34Expr 3 6 k = trans34_r3_6 k := by decide +kernel
lemma trans34_r3_7_eq : ∀ k : Fin 16, trans34Expr 3 7 k = trans34_r3_7 k := by decide +kernel
lemma trans34_r3_8_eq : ∀ k : Fin 16, trans34Expr 3 8 k = trans34_r3_8 k := by decide +kernel
lemma trans34_r3_9_eq : ∀ k : Fin 16, trans34Expr 3 9 k = trans34_r3_9 k := by decide +kernel
lemma trans34_r3_10_eq : ∀ k : Fin 16, trans34Expr 3 10 k = trans34_r3_10 k := by decide +kernel
lemma trans34_r3_11_eq : ∀ k : Fin 16, trans34Expr 3 11 k = trans34_r3_11 k := by decide +kernel
lemma trans34_r3_12_eq : ∀ k : Fin 16, trans34Expr 3 12 k = trans34_r3_12 k := by decide +kernel
lemma trans34_r3_13_eq : ∀ k : Fin 16, trans34Expr 3 13 k = trans34_r3_13 k := by decide +kernel
lemma trans34_r3_14_eq : ∀ k : Fin 16, trans34Expr 3 14 k = trans34_r3_14 k := by decide +kernel
lemma trans34_r3_15_eq : ∀ k : Fin 16, trans34Expr 3 15 k = trans34_r3_15 k := by decide +kernel
lemma trans34_r3_eq (i k : Fin 16) : trans34Expr 3 i k = trans34_r3 i k := by
  fin_cases i
  · exact trans34_r3_0_eq k
  · exact trans34_r3_1_eq k
  · exact trans34_r3_2_eq k
  · exact trans34_r3_3_eq k
  · exact trans34_r3_4_eq k
  · exact trans34_r3_5_eq k
  · exact trans34_r3_6_eq k
  · exact trans34_r3_7_eq k
  · exact trans34_r3_8_eq k
  · exact trans34_r3_9_eq k
  · exact trans34_r3_10_eq k
  · exact trans34_r3_11_eq k
  · exact trans34_r3_12_eq k
  · exact trans34_r3_13_eq k
  · exact trans34_r3_14_eq k
  · exact trans34_r3_15_eq k
lemma trans34_r4_0_eq : ∀ k : Fin 16, trans34Expr 4 0 k = trans34_r4_0 k := by decide +kernel
lemma trans34_r4_1_eq : ∀ k : Fin 16, trans34Expr 4 1 k = trans34_r4_1 k := by decide +kernel
lemma trans34_r4_2_eq : ∀ k : Fin 16, trans34Expr 4 2 k = trans34_r4_2 k := by decide +kernel
lemma trans34_r4_3_eq : ∀ k : Fin 16, trans34Expr 4 3 k = trans34_r4_3 k := by decide +kernel
lemma trans34_r4_4_eq : ∀ k : Fin 16, trans34Expr 4 4 k = trans34_r4_4 k := by decide +kernel
lemma trans34_r4_5_eq : ∀ k : Fin 16, trans34Expr 4 5 k = trans34_r4_5 k := by decide +kernel
lemma trans34_r4_6_eq : ∀ k : Fin 16, trans34Expr 4 6 k = trans34_r4_6 k := by decide +kernel
lemma trans34_r4_7_eq : ∀ k : Fin 16, trans34Expr 4 7 k = trans34_r4_7 k := by decide +kernel
lemma trans34_r4_8_eq : ∀ k : Fin 16, trans34Expr 4 8 k = trans34_r4_8 k := by decide +kernel
lemma trans34_r4_9_eq : ∀ k : Fin 16, trans34Expr 4 9 k = trans34_r4_9 k := by decide +kernel
lemma trans34_r4_10_eq : ∀ k : Fin 16, trans34Expr 4 10 k = trans34_r4_10 k := by decide +kernel
lemma trans34_r4_11_eq : ∀ k : Fin 16, trans34Expr 4 11 k = trans34_r4_11 k := by decide +kernel
lemma trans34_r4_12_eq : ∀ k : Fin 16, trans34Expr 4 12 k = trans34_r4_12 k := by decide +kernel
lemma trans34_r4_13_eq : ∀ k : Fin 16, trans34Expr 4 13 k = trans34_r4_13 k := by decide +kernel
lemma trans34_r4_14_eq : ∀ k : Fin 16, trans34Expr 4 14 k = trans34_r4_14 k := by decide +kernel
lemma trans34_r4_15_eq : ∀ k : Fin 16, trans34Expr 4 15 k = trans34_r4_15 k := by decide +kernel
lemma trans34_r4_eq (i k : Fin 16) : trans34Expr 4 i k = trans34_r4 i k := by
  fin_cases i
  · exact trans34_r4_0_eq k
  · exact trans34_r4_1_eq k
  · exact trans34_r4_2_eq k
  · exact trans34_r4_3_eq k
  · exact trans34_r4_4_eq k
  · exact trans34_r4_5_eq k
  · exact trans34_r4_6_eq k
  · exact trans34_r4_7_eq k
  · exact trans34_r4_8_eq k
  · exact trans34_r4_9_eq k
  · exact trans34_r4_10_eq k
  · exact trans34_r4_11_eq k
  · exact trans34_r4_12_eq k
  · exact trans34_r4_13_eq k
  · exact trans34_r4_14_eq k
  · exact trans34_r4_15_eq k
lemma trans34_r5_0_eq : ∀ k : Fin 16, trans34Expr 5 0 k = trans34_r5_0 k := by decide +kernel
lemma trans34_r5_1_eq : ∀ k : Fin 16, trans34Expr 5 1 k = trans34_r5_1 k := by decide +kernel
lemma trans34_r5_2_eq : ∀ k : Fin 16, trans34Expr 5 2 k = trans34_r5_2 k := by decide +kernel
lemma trans34_r5_3_eq : ∀ k : Fin 16, trans34Expr 5 3 k = trans34_r5_3 k := by decide +kernel
lemma trans34_r5_4_eq : ∀ k : Fin 16, trans34Expr 5 4 k = trans34_r5_4 k := by decide +kernel
lemma trans34_r5_5_eq : ∀ k : Fin 16, trans34Expr 5 5 k = trans34_r5_5 k := by decide +kernel
lemma trans34_r5_6_eq : ∀ k : Fin 16, trans34Expr 5 6 k = trans34_r5_6 k := by decide +kernel
lemma trans34_r5_7_eq : ∀ k : Fin 16, trans34Expr 5 7 k = trans34_r5_7 k := by decide +kernel
lemma trans34_r5_8_eq : ∀ k : Fin 16, trans34Expr 5 8 k = trans34_r5_8 k := by decide +kernel
lemma trans34_r5_9_eq : ∀ k : Fin 16, trans34Expr 5 9 k = trans34_r5_9 k := by decide +kernel
lemma trans34_r5_10_eq : ∀ k : Fin 16, trans34Expr 5 10 k = trans34_r5_10 k := by decide +kernel
lemma trans34_r5_11_eq : ∀ k : Fin 16, trans34Expr 5 11 k = trans34_r5_11 k := by decide +kernel
lemma trans34_r5_12_eq : ∀ k : Fin 16, trans34Expr 5 12 k = trans34_r5_12 k := by decide +kernel
lemma trans34_r5_13_eq : ∀ k : Fin 16, trans34Expr 5 13 k = trans34_r5_13 k := by decide +kernel
lemma trans34_r5_14_eq : ∀ k : Fin 16, trans34Expr 5 14 k = trans34_r5_14 k := by decide +kernel
lemma trans34_r5_15_eq : ∀ k : Fin 16, trans34Expr 5 15 k = trans34_r5_15 k := by decide +kernel
lemma trans34_r5_eq (i k : Fin 16) : trans34Expr 5 i k = trans34_r5 i k := by
  fin_cases i
  · exact trans34_r5_0_eq k
  · exact trans34_r5_1_eq k
  · exact trans34_r5_2_eq k
  · exact trans34_r5_3_eq k
  · exact trans34_r5_4_eq k
  · exact trans34_r5_5_eq k
  · exact trans34_r5_6_eq k
  · exact trans34_r5_7_eq k
  · exact trans34_r5_8_eq k
  · exact trans34_r5_9_eq k
  · exact trans34_r5_10_eq k
  · exact trans34_r5_11_eq k
  · exact trans34_r5_12_eq k
  · exact trans34_r5_13_eq k
  · exact trans34_r5_14_eq k
  · exact trans34_r5_15_eq k
lemma trans34_eq (j : Fin 6) (i k : Fin 16) : trans34Expr j i k = trans34 j i k := by
  fin_cases j
  · exact trans34_r0_eq i k
  · exact trans34_r1_eq i k
  · exact trans34_r2_eq i k
  · exact trans34_r3_eq i k
  · exact trans34_r4_eq i k
  · exact trans34_r5_eq i k
lemma trans34_contains (j : Fin 6) (i k : Fin 16) :
    (trans34 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(34:ℕ))) := by
  rw [← trans34_eq]
  unfold trans34Expr
  convert exp_transformed_step (trans33_contains j i k) (transStep_contains_g j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
lemma trans35_r0_0_eq : ∀ k : Fin 16, trans35Expr 0 0 k = trans35_r0_0 k := by decide +kernel
lemma trans35_r0_1_eq : ∀ k : Fin 16, trans35Expr 0 1 k = trans35_r0_1 k := by decide +kernel
lemma trans35_r0_2_eq : ∀ k : Fin 16, trans35Expr 0 2 k = trans35_r0_2 k := by decide +kernel
lemma trans35_r0_3_eq : ∀ k : Fin 16, trans35Expr 0 3 k = trans35_r0_3 k := by decide +kernel
lemma trans35_r0_4_eq : ∀ k : Fin 16, trans35Expr 0 4 k = trans35_r0_4 k := by decide +kernel
lemma trans35_r0_5_eq : ∀ k : Fin 16, trans35Expr 0 5 k = trans35_r0_5 k := by decide +kernel
lemma trans35_r0_6_eq : ∀ k : Fin 16, trans35Expr 0 6 k = trans35_r0_6 k := by decide +kernel
lemma trans35_r0_7_eq : ∀ k : Fin 16, trans35Expr 0 7 k = trans35_r0_7 k := by decide +kernel
lemma trans35_r0_8_eq : ∀ k : Fin 16, trans35Expr 0 8 k = trans35_r0_8 k := by decide +kernel
lemma trans35_r0_9_eq : ∀ k : Fin 16, trans35Expr 0 9 k = trans35_r0_9 k := by decide +kernel
lemma trans35_r0_10_eq : ∀ k : Fin 16, trans35Expr 0 10 k = trans35_r0_10 k := by decide +kernel
lemma trans35_r0_11_eq : ∀ k : Fin 16, trans35Expr 0 11 k = trans35_r0_11 k := by decide +kernel
lemma trans35_r0_12_eq : ∀ k : Fin 16, trans35Expr 0 12 k = trans35_r0_12 k := by decide +kernel
lemma trans35_r0_13_eq : ∀ k : Fin 16, trans35Expr 0 13 k = trans35_r0_13 k := by decide +kernel
lemma trans35_r0_14_eq : ∀ k : Fin 16, trans35Expr 0 14 k = trans35_r0_14 k := by decide +kernel
lemma trans35_r0_15_eq : ∀ k : Fin 16, trans35Expr 0 15 k = trans35_r0_15 k := by decide +kernel
lemma trans35_r0_eq (i k : Fin 16) : trans35Expr 0 i k = trans35_r0 i k := by
  fin_cases i
  · exact trans35_r0_0_eq k
  · exact trans35_r0_1_eq k
  · exact trans35_r0_2_eq k
  · exact trans35_r0_3_eq k
  · exact trans35_r0_4_eq k
  · exact trans35_r0_5_eq k
  · exact trans35_r0_6_eq k
  · exact trans35_r0_7_eq k
  · exact trans35_r0_8_eq k
  · exact trans35_r0_9_eq k
  · exact trans35_r0_10_eq k
  · exact trans35_r0_11_eq k
  · exact trans35_r0_12_eq k
  · exact trans35_r0_13_eq k
  · exact trans35_r0_14_eq k
  · exact trans35_r0_15_eq k
lemma trans35_r1_0_eq : ∀ k : Fin 16, trans35Expr 1 0 k = trans35_r1_0 k := by decide +kernel
lemma trans35_r1_1_eq : ∀ k : Fin 16, trans35Expr 1 1 k = trans35_r1_1 k := by decide +kernel
lemma trans35_r1_2_eq : ∀ k : Fin 16, trans35Expr 1 2 k = trans35_r1_2 k := by decide +kernel
lemma trans35_r1_3_eq : ∀ k : Fin 16, trans35Expr 1 3 k = trans35_r1_3 k := by decide +kernel
lemma trans35_r1_4_eq : ∀ k : Fin 16, trans35Expr 1 4 k = trans35_r1_4 k := by decide +kernel
lemma trans35_r1_5_eq : ∀ k : Fin 16, trans35Expr 1 5 k = trans35_r1_5 k := by decide +kernel
lemma trans35_r1_6_eq : ∀ k : Fin 16, trans35Expr 1 6 k = trans35_r1_6 k := by decide +kernel
lemma trans35_r1_7_eq : ∀ k : Fin 16, trans35Expr 1 7 k = trans35_r1_7 k := by decide +kernel
lemma trans35_r1_8_eq : ∀ k : Fin 16, trans35Expr 1 8 k = trans35_r1_8 k := by decide +kernel
lemma trans35_r1_9_eq : ∀ k : Fin 16, trans35Expr 1 9 k = trans35_r1_9 k := by decide +kernel
lemma trans35_r1_10_eq : ∀ k : Fin 16, trans35Expr 1 10 k = trans35_r1_10 k := by decide +kernel
lemma trans35_r1_11_eq : ∀ k : Fin 16, trans35Expr 1 11 k = trans35_r1_11 k := by decide +kernel
lemma trans35_r1_12_eq : ∀ k : Fin 16, trans35Expr 1 12 k = trans35_r1_12 k := by decide +kernel
lemma trans35_r1_13_eq : ∀ k : Fin 16, trans35Expr 1 13 k = trans35_r1_13 k := by decide +kernel
lemma trans35_r1_14_eq : ∀ k : Fin 16, trans35Expr 1 14 k = trans35_r1_14 k := by decide +kernel
lemma trans35_r1_15_eq : ∀ k : Fin 16, trans35Expr 1 15 k = trans35_r1_15 k := by decide +kernel
lemma trans35_r1_eq (i k : Fin 16) : trans35Expr 1 i k = trans35_r1 i k := by
  fin_cases i
  · exact trans35_r1_0_eq k
  · exact trans35_r1_1_eq k
  · exact trans35_r1_2_eq k
  · exact trans35_r1_3_eq k
  · exact trans35_r1_4_eq k
  · exact trans35_r1_5_eq k
  · exact trans35_r1_6_eq k
  · exact trans35_r1_7_eq k
  · exact trans35_r1_8_eq k
  · exact trans35_r1_9_eq k
  · exact trans35_r1_10_eq k
  · exact trans35_r1_11_eq k
  · exact trans35_r1_12_eq k
  · exact trans35_r1_13_eq k
  · exact trans35_r1_14_eq k
  · exact trans35_r1_15_eq k
lemma trans35_r2_0_eq : ∀ k : Fin 16, trans35Expr 2 0 k = trans35_r2_0 k := by decide +kernel
lemma trans35_r2_1_eq : ∀ k : Fin 16, trans35Expr 2 1 k = trans35_r2_1 k := by decide +kernel
lemma trans35_r2_2_eq : ∀ k : Fin 16, trans35Expr 2 2 k = trans35_r2_2 k := by decide +kernel
lemma trans35_r2_3_eq : ∀ k : Fin 16, trans35Expr 2 3 k = trans35_r2_3 k := by decide +kernel
lemma trans35_r2_4_eq : ∀ k : Fin 16, trans35Expr 2 4 k = trans35_r2_4 k := by decide +kernel
lemma trans35_r2_5_eq : ∀ k : Fin 16, trans35Expr 2 5 k = trans35_r2_5 k := by decide +kernel
lemma trans35_r2_6_eq : ∀ k : Fin 16, trans35Expr 2 6 k = trans35_r2_6 k := by decide +kernel
lemma trans35_r2_7_eq : ∀ k : Fin 16, trans35Expr 2 7 k = trans35_r2_7 k := by decide +kernel
lemma trans35_r2_8_eq : ∀ k : Fin 16, trans35Expr 2 8 k = trans35_r2_8 k := by decide +kernel
lemma trans35_r2_9_eq : ∀ k : Fin 16, trans35Expr 2 9 k = trans35_r2_9 k := by decide +kernel
lemma trans35_r2_10_eq : ∀ k : Fin 16, trans35Expr 2 10 k = trans35_r2_10 k := by decide +kernel
lemma trans35_r2_11_eq : ∀ k : Fin 16, trans35Expr 2 11 k = trans35_r2_11 k := by decide +kernel
lemma trans35_r2_12_eq : ∀ k : Fin 16, trans35Expr 2 12 k = trans35_r2_12 k := by decide +kernel
lemma trans35_r2_13_eq : ∀ k : Fin 16, trans35Expr 2 13 k = trans35_r2_13 k := by decide +kernel
lemma trans35_r2_14_eq : ∀ k : Fin 16, trans35Expr 2 14 k = trans35_r2_14 k := by decide +kernel
lemma trans35_r2_15_eq : ∀ k : Fin 16, trans35Expr 2 15 k = trans35_r2_15 k := by decide +kernel
lemma trans35_r2_eq (i k : Fin 16) : trans35Expr 2 i k = trans35_r2 i k := by
  fin_cases i
  · exact trans35_r2_0_eq k
  · exact trans35_r2_1_eq k
  · exact trans35_r2_2_eq k
  · exact trans35_r2_3_eq k
  · exact trans35_r2_4_eq k
  · exact trans35_r2_5_eq k
  · exact trans35_r2_6_eq k
  · exact trans35_r2_7_eq k
  · exact trans35_r2_8_eq k
  · exact trans35_r2_9_eq k
  · exact trans35_r2_10_eq k
  · exact trans35_r2_11_eq k
  · exact trans35_r2_12_eq k
  · exact trans35_r2_13_eq k
  · exact trans35_r2_14_eq k
  · exact trans35_r2_15_eq k
lemma trans35_r3_0_eq : ∀ k : Fin 16, trans35Expr 3 0 k = trans35_r3_0 k := by decide +kernel
lemma trans35_r3_1_eq : ∀ k : Fin 16, trans35Expr 3 1 k = trans35_r3_1 k := by decide +kernel
lemma trans35_r3_2_eq : ∀ k : Fin 16, trans35Expr 3 2 k = trans35_r3_2 k := by decide +kernel
lemma trans35_r3_3_eq : ∀ k : Fin 16, trans35Expr 3 3 k = trans35_r3_3 k := by decide +kernel
lemma trans35_r3_4_eq : ∀ k : Fin 16, trans35Expr 3 4 k = trans35_r3_4 k := by decide +kernel
lemma trans35_r3_5_eq : ∀ k : Fin 16, trans35Expr 3 5 k = trans35_r3_5 k := by decide +kernel
lemma trans35_r3_6_eq : ∀ k : Fin 16, trans35Expr 3 6 k = trans35_r3_6 k := by decide +kernel
lemma trans35_r3_7_eq : ∀ k : Fin 16, trans35Expr 3 7 k = trans35_r3_7 k := by decide +kernel
lemma trans35_r3_8_eq : ∀ k : Fin 16, trans35Expr 3 8 k = trans35_r3_8 k := by decide +kernel
lemma trans35_r3_9_eq : ∀ k : Fin 16, trans35Expr 3 9 k = trans35_r3_9 k := by decide +kernel
lemma trans35_r3_10_eq : ∀ k : Fin 16, trans35Expr 3 10 k = trans35_r3_10 k := by decide +kernel
lemma trans35_r3_11_eq : ∀ k : Fin 16, trans35Expr 3 11 k = trans35_r3_11 k := by decide +kernel
lemma trans35_r3_12_eq : ∀ k : Fin 16, trans35Expr 3 12 k = trans35_r3_12 k := by decide +kernel
lemma trans35_r3_13_eq : ∀ k : Fin 16, trans35Expr 3 13 k = trans35_r3_13 k := by decide +kernel
lemma trans35_r3_14_eq : ∀ k : Fin 16, trans35Expr 3 14 k = trans35_r3_14 k := by decide +kernel
lemma trans35_r3_15_eq : ∀ k : Fin 16, trans35Expr 3 15 k = trans35_r3_15 k := by decide +kernel
lemma trans35_r3_eq (i k : Fin 16) : trans35Expr 3 i k = trans35_r3 i k := by
  fin_cases i
  · exact trans35_r3_0_eq k
  · exact trans35_r3_1_eq k
  · exact trans35_r3_2_eq k
  · exact trans35_r3_3_eq k
  · exact trans35_r3_4_eq k
  · exact trans35_r3_5_eq k
  · exact trans35_r3_6_eq k
  · exact trans35_r3_7_eq k
  · exact trans35_r3_8_eq k
  · exact trans35_r3_9_eq k
  · exact trans35_r3_10_eq k
  · exact trans35_r3_11_eq k
  · exact trans35_r3_12_eq k
  · exact trans35_r3_13_eq k
  · exact trans35_r3_14_eq k
  · exact trans35_r3_15_eq k
lemma trans35_r4_0_eq : ∀ k : Fin 16, trans35Expr 4 0 k = trans35_r4_0 k := by decide +kernel
lemma trans35_r4_1_eq : ∀ k : Fin 16, trans35Expr 4 1 k = trans35_r4_1 k := by decide +kernel
lemma trans35_r4_2_eq : ∀ k : Fin 16, trans35Expr 4 2 k = trans35_r4_2 k := by decide +kernel
lemma trans35_r4_3_eq : ∀ k : Fin 16, trans35Expr 4 3 k = trans35_r4_3 k := by decide +kernel
lemma trans35_r4_4_eq : ∀ k : Fin 16, trans35Expr 4 4 k = trans35_r4_4 k := by decide +kernel
lemma trans35_r4_5_eq : ∀ k : Fin 16, trans35Expr 4 5 k = trans35_r4_5 k := by decide +kernel
lemma trans35_r4_6_eq : ∀ k : Fin 16, trans35Expr 4 6 k = trans35_r4_6 k := by decide +kernel
lemma trans35_r4_7_eq : ∀ k : Fin 16, trans35Expr 4 7 k = trans35_r4_7 k := by decide +kernel
lemma trans35_r4_8_eq : ∀ k : Fin 16, trans35Expr 4 8 k = trans35_r4_8 k := by decide +kernel
lemma trans35_r4_9_eq : ∀ k : Fin 16, trans35Expr 4 9 k = trans35_r4_9 k := by decide +kernel
lemma trans35_r4_10_eq : ∀ k : Fin 16, trans35Expr 4 10 k = trans35_r4_10 k := by decide +kernel
lemma trans35_r4_11_eq : ∀ k : Fin 16, trans35Expr 4 11 k = trans35_r4_11 k := by decide +kernel
lemma trans35_r4_12_eq : ∀ k : Fin 16, trans35Expr 4 12 k = trans35_r4_12 k := by decide +kernel
lemma trans35_r4_13_eq : ∀ k : Fin 16, trans35Expr 4 13 k = trans35_r4_13 k := by decide +kernel
lemma trans35_r4_14_eq : ∀ k : Fin 16, trans35Expr 4 14 k = trans35_r4_14 k := by decide +kernel
lemma trans35_r4_15_eq : ∀ k : Fin 16, trans35Expr 4 15 k = trans35_r4_15 k := by decide +kernel
lemma trans35_r4_eq (i k : Fin 16) : trans35Expr 4 i k = trans35_r4 i k := by
  fin_cases i
  · exact trans35_r4_0_eq k
  · exact trans35_r4_1_eq k
  · exact trans35_r4_2_eq k
  · exact trans35_r4_3_eq k
  · exact trans35_r4_4_eq k
  · exact trans35_r4_5_eq k
  · exact trans35_r4_6_eq k
  · exact trans35_r4_7_eq k
  · exact trans35_r4_8_eq k
  · exact trans35_r4_9_eq k
  · exact trans35_r4_10_eq k
  · exact trans35_r4_11_eq k
  · exact trans35_r4_12_eq k
  · exact trans35_r4_13_eq k
  · exact trans35_r4_14_eq k
  · exact trans35_r4_15_eq k
lemma trans35_r5_0_eq : ∀ k : Fin 16, trans35Expr 5 0 k = trans35_r5_0 k := by decide +kernel
lemma trans35_r5_1_eq : ∀ k : Fin 16, trans35Expr 5 1 k = trans35_r5_1 k := by decide +kernel
lemma trans35_r5_2_eq : ∀ k : Fin 16, trans35Expr 5 2 k = trans35_r5_2 k := by decide +kernel
lemma trans35_r5_3_eq : ∀ k : Fin 16, trans35Expr 5 3 k = trans35_r5_3 k := by decide +kernel
lemma trans35_r5_4_eq : ∀ k : Fin 16, trans35Expr 5 4 k = trans35_r5_4 k := by decide +kernel
lemma trans35_r5_5_eq : ∀ k : Fin 16, trans35Expr 5 5 k = trans35_r5_5 k := by decide +kernel
lemma trans35_r5_6_eq : ∀ k : Fin 16, trans35Expr 5 6 k = trans35_r5_6 k := by decide +kernel
lemma trans35_r5_7_eq : ∀ k : Fin 16, trans35Expr 5 7 k = trans35_r5_7 k := by decide +kernel
lemma trans35_r5_8_eq : ∀ k : Fin 16, trans35Expr 5 8 k = trans35_r5_8 k := by decide +kernel
lemma trans35_r5_9_eq : ∀ k : Fin 16, trans35Expr 5 9 k = trans35_r5_9 k := by decide +kernel
lemma trans35_r5_10_eq : ∀ k : Fin 16, trans35Expr 5 10 k = trans35_r5_10 k := by decide +kernel
lemma trans35_r5_11_eq : ∀ k : Fin 16, trans35Expr 5 11 k = trans35_r5_11 k := by decide +kernel
lemma trans35_r5_12_eq : ∀ k : Fin 16, trans35Expr 5 12 k = trans35_r5_12 k := by decide +kernel
lemma trans35_r5_13_eq : ∀ k : Fin 16, trans35Expr 5 13 k = trans35_r5_13 k := by decide +kernel
lemma trans35_r5_14_eq : ∀ k : Fin 16, trans35Expr 5 14 k = trans35_r5_14 k := by decide +kernel
lemma trans35_r5_15_eq : ∀ k : Fin 16, trans35Expr 5 15 k = trans35_r5_15 k := by decide +kernel
lemma trans35_r5_eq (i k : Fin 16) : trans35Expr 5 i k = trans35_r5 i k := by
  fin_cases i
  · exact trans35_r5_0_eq k
  · exact trans35_r5_1_eq k
  · exact trans35_r5_2_eq k
  · exact trans35_r5_3_eq k
  · exact trans35_r5_4_eq k
  · exact trans35_r5_5_eq k
  · exact trans35_r5_6_eq k
  · exact trans35_r5_7_eq k
  · exact trans35_r5_8_eq k
  · exact trans35_r5_9_eq k
  · exact trans35_r5_10_eq k
  · exact trans35_r5_11_eq k
  · exact trans35_r5_12_eq k
  · exact trans35_r5_13_eq k
  · exact trans35_r5_14_eq k
  · exact trans35_r5_15_eq k
lemma trans35_eq (j : Fin 6) (i k : Fin 16) : trans35Expr j i k = trans35 j i k := by
  fin_cases j
  · exact trans35_r0_eq i k
  · exact trans35_r1_eq i k
  · exact trans35_r2_eq i k
  · exact trans35_r3_eq i k
  · exact trans35_r4_eq i k
  · exact trans35_r5_eq i k
lemma trans35_contains (j : Fin 6) (i k : Fin 16) :
    (trans35 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(35:ℕ))) := by
  rw [← trans35_eq]
  unfold trans35Expr
  convert exp_transformed_step (trans34_contains j i k) (transStep_contains_g j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
lemma trans36_r0_0_eq : ∀ k : Fin 16, trans36Expr 0 0 k = trans36_r0_0 k := by decide +kernel
lemma trans36_r0_1_eq : ∀ k : Fin 16, trans36Expr 0 1 k = trans36_r0_1 k := by decide +kernel
lemma trans36_r0_2_eq : ∀ k : Fin 16, trans36Expr 0 2 k = trans36_r0_2 k := by decide +kernel
lemma trans36_r0_3_eq : ∀ k : Fin 16, trans36Expr 0 3 k = trans36_r0_3 k := by decide +kernel
lemma trans36_r0_4_eq : ∀ k : Fin 16, trans36Expr 0 4 k = trans36_r0_4 k := by decide +kernel
lemma trans36_r0_5_eq : ∀ k : Fin 16, trans36Expr 0 5 k = trans36_r0_5 k := by decide +kernel
lemma trans36_r0_6_eq : ∀ k : Fin 16, trans36Expr 0 6 k = trans36_r0_6 k := by decide +kernel
lemma trans36_r0_7_eq : ∀ k : Fin 16, trans36Expr 0 7 k = trans36_r0_7 k := by decide +kernel
lemma trans36_r0_8_eq : ∀ k : Fin 16, trans36Expr 0 8 k = trans36_r0_8 k := by decide +kernel
lemma trans36_r0_9_eq : ∀ k : Fin 16, trans36Expr 0 9 k = trans36_r0_9 k := by decide +kernel
lemma trans36_r0_10_eq : ∀ k : Fin 16, trans36Expr 0 10 k = trans36_r0_10 k := by decide +kernel
lemma trans36_r0_11_eq : ∀ k : Fin 16, trans36Expr 0 11 k = trans36_r0_11 k := by decide +kernel
lemma trans36_r0_12_eq : ∀ k : Fin 16, trans36Expr 0 12 k = trans36_r0_12 k := by decide +kernel
lemma trans36_r0_13_eq : ∀ k : Fin 16, trans36Expr 0 13 k = trans36_r0_13 k := by decide +kernel
lemma trans36_r0_14_eq : ∀ k : Fin 16, trans36Expr 0 14 k = trans36_r0_14 k := by decide +kernel
lemma trans36_r0_15_eq : ∀ k : Fin 16, trans36Expr 0 15 k = trans36_r0_15 k := by decide +kernel
lemma trans36_r0_eq (i k : Fin 16) : trans36Expr 0 i k = trans36_r0 i k := by
  fin_cases i
  · exact trans36_r0_0_eq k
  · exact trans36_r0_1_eq k
  · exact trans36_r0_2_eq k
  · exact trans36_r0_3_eq k
  · exact trans36_r0_4_eq k
  · exact trans36_r0_5_eq k
  · exact trans36_r0_6_eq k
  · exact trans36_r0_7_eq k
  · exact trans36_r0_8_eq k
  · exact trans36_r0_9_eq k
  · exact trans36_r0_10_eq k
  · exact trans36_r0_11_eq k
  · exact trans36_r0_12_eq k
  · exact trans36_r0_13_eq k
  · exact trans36_r0_14_eq k
  · exact trans36_r0_15_eq k
lemma trans36_r1_0_eq : ∀ k : Fin 16, trans36Expr 1 0 k = trans36_r1_0 k := by decide +kernel
lemma trans36_r1_1_eq : ∀ k : Fin 16, trans36Expr 1 1 k = trans36_r1_1 k := by decide +kernel
lemma trans36_r1_2_eq : ∀ k : Fin 16, trans36Expr 1 2 k = trans36_r1_2 k := by decide +kernel
lemma trans36_r1_3_eq : ∀ k : Fin 16, trans36Expr 1 3 k = trans36_r1_3 k := by decide +kernel
lemma trans36_r1_4_eq : ∀ k : Fin 16, trans36Expr 1 4 k = trans36_r1_4 k := by decide +kernel
lemma trans36_r1_5_eq : ∀ k : Fin 16, trans36Expr 1 5 k = trans36_r1_5 k := by decide +kernel
lemma trans36_r1_6_eq : ∀ k : Fin 16, trans36Expr 1 6 k = trans36_r1_6 k := by decide +kernel
lemma trans36_r1_7_eq : ∀ k : Fin 16, trans36Expr 1 7 k = trans36_r1_7 k := by decide +kernel
lemma trans36_r1_8_eq : ∀ k : Fin 16, trans36Expr 1 8 k = trans36_r1_8 k := by decide +kernel
lemma trans36_r1_9_eq : ∀ k : Fin 16, trans36Expr 1 9 k = trans36_r1_9 k := by decide +kernel
lemma trans36_r1_10_eq : ∀ k : Fin 16, trans36Expr 1 10 k = trans36_r1_10 k := by decide +kernel
lemma trans36_r1_11_eq : ∀ k : Fin 16, trans36Expr 1 11 k = trans36_r1_11 k := by decide +kernel
lemma trans36_r1_12_eq : ∀ k : Fin 16, trans36Expr 1 12 k = trans36_r1_12 k := by decide +kernel
lemma trans36_r1_13_eq : ∀ k : Fin 16, trans36Expr 1 13 k = trans36_r1_13 k := by decide +kernel
lemma trans36_r1_14_eq : ∀ k : Fin 16, trans36Expr 1 14 k = trans36_r1_14 k := by decide +kernel
lemma trans36_r1_15_eq : ∀ k : Fin 16, trans36Expr 1 15 k = trans36_r1_15 k := by decide +kernel
lemma trans36_r1_eq (i k : Fin 16) : trans36Expr 1 i k = trans36_r1 i k := by
  fin_cases i
  · exact trans36_r1_0_eq k
  · exact trans36_r1_1_eq k
  · exact trans36_r1_2_eq k
  · exact trans36_r1_3_eq k
  · exact trans36_r1_4_eq k
  · exact trans36_r1_5_eq k
  · exact trans36_r1_6_eq k
  · exact trans36_r1_7_eq k
  · exact trans36_r1_8_eq k
  · exact trans36_r1_9_eq k
  · exact trans36_r1_10_eq k
  · exact trans36_r1_11_eq k
  · exact trans36_r1_12_eq k
  · exact trans36_r1_13_eq k
  · exact trans36_r1_14_eq k
  · exact trans36_r1_15_eq k
lemma trans36_r2_0_eq : ∀ k : Fin 16, trans36Expr 2 0 k = trans36_r2_0 k := by decide +kernel
lemma trans36_r2_1_eq : ∀ k : Fin 16, trans36Expr 2 1 k = trans36_r2_1 k := by decide +kernel
lemma trans36_r2_2_eq : ∀ k : Fin 16, trans36Expr 2 2 k = trans36_r2_2 k := by decide +kernel
lemma trans36_r2_3_eq : ∀ k : Fin 16, trans36Expr 2 3 k = trans36_r2_3 k := by decide +kernel
lemma trans36_r2_4_eq : ∀ k : Fin 16, trans36Expr 2 4 k = trans36_r2_4 k := by decide +kernel
lemma trans36_r2_5_eq : ∀ k : Fin 16, trans36Expr 2 5 k = trans36_r2_5 k := by decide +kernel
lemma trans36_r2_6_eq : ∀ k : Fin 16, trans36Expr 2 6 k = trans36_r2_6 k := by decide +kernel
lemma trans36_r2_7_eq : ∀ k : Fin 16, trans36Expr 2 7 k = trans36_r2_7 k := by decide +kernel
lemma trans36_r2_8_eq : ∀ k : Fin 16, trans36Expr 2 8 k = trans36_r2_8 k := by decide +kernel
lemma trans36_r2_9_eq : ∀ k : Fin 16, trans36Expr 2 9 k = trans36_r2_9 k := by decide +kernel
lemma trans36_r2_10_eq : ∀ k : Fin 16, trans36Expr 2 10 k = trans36_r2_10 k := by decide +kernel
lemma trans36_r2_11_eq : ∀ k : Fin 16, trans36Expr 2 11 k = trans36_r2_11 k := by decide +kernel
lemma trans36_r2_12_eq : ∀ k : Fin 16, trans36Expr 2 12 k = trans36_r2_12 k := by decide +kernel
lemma trans36_r2_13_eq : ∀ k : Fin 16, trans36Expr 2 13 k = trans36_r2_13 k := by decide +kernel
lemma trans36_r2_14_eq : ∀ k : Fin 16, trans36Expr 2 14 k = trans36_r2_14 k := by decide +kernel
lemma trans36_r2_15_eq : ∀ k : Fin 16, trans36Expr 2 15 k = trans36_r2_15 k := by decide +kernel
lemma trans36_r2_eq (i k : Fin 16) : trans36Expr 2 i k = trans36_r2 i k := by
  fin_cases i
  · exact trans36_r2_0_eq k
  · exact trans36_r2_1_eq k
  · exact trans36_r2_2_eq k
  · exact trans36_r2_3_eq k
  · exact trans36_r2_4_eq k
  · exact trans36_r2_5_eq k
  · exact trans36_r2_6_eq k
  · exact trans36_r2_7_eq k
  · exact trans36_r2_8_eq k
  · exact trans36_r2_9_eq k
  · exact trans36_r2_10_eq k
  · exact trans36_r2_11_eq k
  · exact trans36_r2_12_eq k
  · exact trans36_r2_13_eq k
  · exact trans36_r2_14_eq k
  · exact trans36_r2_15_eq k
lemma trans36_r3_0_eq : ∀ k : Fin 16, trans36Expr 3 0 k = trans36_r3_0 k := by decide +kernel
lemma trans36_r3_1_eq : ∀ k : Fin 16, trans36Expr 3 1 k = trans36_r3_1 k := by decide +kernel
lemma trans36_r3_2_eq : ∀ k : Fin 16, trans36Expr 3 2 k = trans36_r3_2 k := by decide +kernel
lemma trans36_r3_3_eq : ∀ k : Fin 16, trans36Expr 3 3 k = trans36_r3_3 k := by decide +kernel
lemma trans36_r3_4_eq : ∀ k : Fin 16, trans36Expr 3 4 k = trans36_r3_4 k := by decide +kernel
lemma trans36_r3_5_eq : ∀ k : Fin 16, trans36Expr 3 5 k = trans36_r3_5 k := by decide +kernel
lemma trans36_r3_6_eq : ∀ k : Fin 16, trans36Expr 3 6 k = trans36_r3_6 k := by decide +kernel
lemma trans36_r3_7_eq : ∀ k : Fin 16, trans36Expr 3 7 k = trans36_r3_7 k := by decide +kernel
lemma trans36_r3_8_eq : ∀ k : Fin 16, trans36Expr 3 8 k = trans36_r3_8 k := by decide +kernel
lemma trans36_r3_9_eq : ∀ k : Fin 16, trans36Expr 3 9 k = trans36_r3_9 k := by decide +kernel
lemma trans36_r3_10_eq : ∀ k : Fin 16, trans36Expr 3 10 k = trans36_r3_10 k := by decide +kernel
lemma trans36_r3_11_eq : ∀ k : Fin 16, trans36Expr 3 11 k = trans36_r3_11 k := by decide +kernel
lemma trans36_r3_12_eq : ∀ k : Fin 16, trans36Expr 3 12 k = trans36_r3_12 k := by decide +kernel
lemma trans36_r3_13_eq : ∀ k : Fin 16, trans36Expr 3 13 k = trans36_r3_13 k := by decide +kernel
lemma trans36_r3_14_eq : ∀ k : Fin 16, trans36Expr 3 14 k = trans36_r3_14 k := by decide +kernel
lemma trans36_r3_15_eq : ∀ k : Fin 16, trans36Expr 3 15 k = trans36_r3_15 k := by decide +kernel
lemma trans36_r3_eq (i k : Fin 16) : trans36Expr 3 i k = trans36_r3 i k := by
  fin_cases i
  · exact trans36_r3_0_eq k
  · exact trans36_r3_1_eq k
  · exact trans36_r3_2_eq k
  · exact trans36_r3_3_eq k
  · exact trans36_r3_4_eq k
  · exact trans36_r3_5_eq k
  · exact trans36_r3_6_eq k
  · exact trans36_r3_7_eq k
  · exact trans36_r3_8_eq k
  · exact trans36_r3_9_eq k
  · exact trans36_r3_10_eq k
  · exact trans36_r3_11_eq k
  · exact trans36_r3_12_eq k
  · exact trans36_r3_13_eq k
  · exact trans36_r3_14_eq k
  · exact trans36_r3_15_eq k
lemma trans36_r4_0_eq : ∀ k : Fin 16, trans36Expr 4 0 k = trans36_r4_0 k := by decide +kernel
lemma trans36_r4_1_eq : ∀ k : Fin 16, trans36Expr 4 1 k = trans36_r4_1 k := by decide +kernel
lemma trans36_r4_2_eq : ∀ k : Fin 16, trans36Expr 4 2 k = trans36_r4_2 k := by decide +kernel
lemma trans36_r4_3_eq : ∀ k : Fin 16, trans36Expr 4 3 k = trans36_r4_3 k := by decide +kernel
lemma trans36_r4_4_eq : ∀ k : Fin 16, trans36Expr 4 4 k = trans36_r4_4 k := by decide +kernel
lemma trans36_r4_5_eq : ∀ k : Fin 16, trans36Expr 4 5 k = trans36_r4_5 k := by decide +kernel
lemma trans36_r4_6_eq : ∀ k : Fin 16, trans36Expr 4 6 k = trans36_r4_6 k := by decide +kernel
lemma trans36_r4_7_eq : ∀ k : Fin 16, trans36Expr 4 7 k = trans36_r4_7 k := by decide +kernel
lemma trans36_r4_8_eq : ∀ k : Fin 16, trans36Expr 4 8 k = trans36_r4_8 k := by decide +kernel
lemma trans36_r4_9_eq : ∀ k : Fin 16, trans36Expr 4 9 k = trans36_r4_9 k := by decide +kernel
lemma trans36_r4_10_eq : ∀ k : Fin 16, trans36Expr 4 10 k = trans36_r4_10 k := by decide +kernel
lemma trans36_r4_11_eq : ∀ k : Fin 16, trans36Expr 4 11 k = trans36_r4_11 k := by decide +kernel
lemma trans36_r4_12_eq : ∀ k : Fin 16, trans36Expr 4 12 k = trans36_r4_12 k := by decide +kernel
lemma trans36_r4_13_eq : ∀ k : Fin 16, trans36Expr 4 13 k = trans36_r4_13 k := by decide +kernel
lemma trans36_r4_14_eq : ∀ k : Fin 16, trans36Expr 4 14 k = trans36_r4_14 k := by decide +kernel
lemma trans36_r4_15_eq : ∀ k : Fin 16, trans36Expr 4 15 k = trans36_r4_15 k := by decide +kernel
lemma trans36_r4_eq (i k : Fin 16) : trans36Expr 4 i k = trans36_r4 i k := by
  fin_cases i
  · exact trans36_r4_0_eq k
  · exact trans36_r4_1_eq k
  · exact trans36_r4_2_eq k
  · exact trans36_r4_3_eq k
  · exact trans36_r4_4_eq k
  · exact trans36_r4_5_eq k
  · exact trans36_r4_6_eq k
  · exact trans36_r4_7_eq k
  · exact trans36_r4_8_eq k
  · exact trans36_r4_9_eq k
  · exact trans36_r4_10_eq k
  · exact trans36_r4_11_eq k
  · exact trans36_r4_12_eq k
  · exact trans36_r4_13_eq k
  · exact trans36_r4_14_eq k
  · exact trans36_r4_15_eq k
lemma trans36_r5_0_eq : ∀ k : Fin 16, trans36Expr 5 0 k = trans36_r5_0 k := by decide +kernel
lemma trans36_r5_1_eq : ∀ k : Fin 16, trans36Expr 5 1 k = trans36_r5_1 k := by decide +kernel
lemma trans36_r5_2_eq : ∀ k : Fin 16, trans36Expr 5 2 k = trans36_r5_2 k := by decide +kernel
lemma trans36_r5_3_eq : ∀ k : Fin 16, trans36Expr 5 3 k = trans36_r5_3 k := by decide +kernel
lemma trans36_r5_4_eq : ∀ k : Fin 16, trans36Expr 5 4 k = trans36_r5_4 k := by decide +kernel
lemma trans36_r5_5_eq : ∀ k : Fin 16, trans36Expr 5 5 k = trans36_r5_5 k := by decide +kernel
lemma trans36_r5_6_eq : ∀ k : Fin 16, trans36Expr 5 6 k = trans36_r5_6 k := by decide +kernel
lemma trans36_r5_7_eq : ∀ k : Fin 16, trans36Expr 5 7 k = trans36_r5_7 k := by decide +kernel
lemma trans36_r5_8_eq : ∀ k : Fin 16, trans36Expr 5 8 k = trans36_r5_8 k := by decide +kernel
lemma trans36_r5_9_eq : ∀ k : Fin 16, trans36Expr 5 9 k = trans36_r5_9 k := by decide +kernel
lemma trans36_r5_10_eq : ∀ k : Fin 16, trans36Expr 5 10 k = trans36_r5_10 k := by decide +kernel
lemma trans36_r5_11_eq : ∀ k : Fin 16, trans36Expr 5 11 k = trans36_r5_11 k := by decide +kernel
lemma trans36_r5_12_eq : ∀ k : Fin 16, trans36Expr 5 12 k = trans36_r5_12 k := by decide +kernel
lemma trans36_r5_13_eq : ∀ k : Fin 16, trans36Expr 5 13 k = trans36_r5_13 k := by decide +kernel
lemma trans36_r5_14_eq : ∀ k : Fin 16, trans36Expr 5 14 k = trans36_r5_14 k := by decide +kernel
lemma trans36_r5_15_eq : ∀ k : Fin 16, trans36Expr 5 15 k = trans36_r5_15 k := by decide +kernel
lemma trans36_r5_eq (i k : Fin 16) : trans36Expr 5 i k = trans36_r5 i k := by
  fin_cases i
  · exact trans36_r5_0_eq k
  · exact trans36_r5_1_eq k
  · exact trans36_r5_2_eq k
  · exact trans36_r5_3_eq k
  · exact trans36_r5_4_eq k
  · exact trans36_r5_5_eq k
  · exact trans36_r5_6_eq k
  · exact trans36_r5_7_eq k
  · exact trans36_r5_8_eq k
  · exact trans36_r5_9_eq k
  · exact trans36_r5_10_eq k
  · exact trans36_r5_11_eq k
  · exact trans36_r5_12_eq k
  · exact trans36_r5_13_eq k
  · exact trans36_r5_14_eq k
  · exact trans36_r5_15_eq k
lemma trans36_eq (j : Fin 6) (i k : Fin 16) : trans36Expr j i k = trans36 j i k := by
  fin_cases j
  · exact trans36_r0_eq i k
  · exact trans36_r1_eq i k
  · exact trans36_r2_eq i k
  · exact trans36_r3_eq i k
  · exact trans36_r4_eq i k
  · exact trans36_r5_eq i k
lemma trans36_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (trans36 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(36:ℕ))) := by
  rw [← trans36_eq]
  unfold trans36Expr
  convert exp_transformed_step (trans35_contains j i k) (transStep_contains_g j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.trans36_contains_g_oai := @OAI.SharpPlanar.CachedData.trans36_contains_g_oai
