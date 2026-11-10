-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.trans92_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T01:03:22.179197+00:00
-- url     : https://prove2.me/submissions/a73fb34e-fb65-4503-84c8-74e78706d1e5

import Mathlib
import Definitions.Def_OAIQ098G063
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G1633
import Definitions.Def_OAIQ098G1636
import Theorems.Thm_OAI_SharpPlanar_CachedData_trans91_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_g

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

lemma transformedStepBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) :
    (transformedStepBox p).Contains (Complex.exp (Complex.I*Real.pi*z t)) := by
  have hh := CBox.contains_powFast_g hp.2.2.2.2 3 4 (by norm_num)
  rw [← Complex.exp_nat_mul] at hh
  change (p.quarter.powFast 3 4).Contains _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [pointZ_eq_g]
  congr 1
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
lemma transStep_r0_0_eq : ∀ k : Fin 16, transStepExpr 0 0 k = transStep_r0_0 k := by decide +kernel
lemma transStep_r0_1_eq : ∀ k : Fin 16, transStepExpr 0 1 k = transStep_r0_1 k := by decide +kernel
lemma transStep_r0_2_eq : ∀ k : Fin 16, transStepExpr 0 2 k = transStep_r0_2 k := by decide +kernel
lemma transStep_r0_3_eq : ∀ k : Fin 16, transStepExpr 0 3 k = transStep_r0_3 k := by decide +kernel
lemma transStep_r0_4_eq : ∀ k : Fin 16, transStepExpr 0 4 k = transStep_r0_4 k := by decide +kernel
lemma transStep_r0_5_eq : ∀ k : Fin 16, transStepExpr 0 5 k = transStep_r0_5 k := by decide +kernel
lemma transStep_r0_6_eq : ∀ k : Fin 16, transStepExpr 0 6 k = transStep_r0_6 k := by decide +kernel
lemma transStep_r0_7_eq : ∀ k : Fin 16, transStepExpr 0 7 k = transStep_r0_7 k := by decide +kernel
lemma transStep_r0_8_eq : ∀ k : Fin 16, transStepExpr 0 8 k = transStep_r0_8 k := by decide +kernel
lemma transStep_r0_9_eq : ∀ k : Fin 16, transStepExpr 0 9 k = transStep_r0_9 k := by decide +kernel
lemma transStep_r0_10_eq : ∀ k : Fin 16, transStepExpr 0 10 k = transStep_r0_10 k := by decide +kernel
lemma transStep_r0_11_eq : ∀ k : Fin 16, transStepExpr 0 11 k = transStep_r0_11 k := by decide +kernel
lemma transStep_r0_12_eq : ∀ k : Fin 16, transStepExpr 0 12 k = transStep_r0_12 k := by decide +kernel
lemma transStep_r0_13_eq : ∀ k : Fin 16, transStepExpr 0 13 k = transStep_r0_13 k := by decide +kernel
lemma transStep_r0_14_eq : ∀ k : Fin 16, transStepExpr 0 14 k = transStep_r0_14 k := by decide +kernel
lemma transStep_r0_15_eq : ∀ k : Fin 16, transStepExpr 0 15 k = transStep_r0_15 k := by decide +kernel
lemma transStep_r0_eq (i k : Fin 16) : transStepExpr 0 i k = transStep_r0 i k := by
  fin_cases i
  · exact transStep_r0_0_eq k
  · exact transStep_r0_1_eq k
  · exact transStep_r0_2_eq k
  · exact transStep_r0_3_eq k
  · exact transStep_r0_4_eq k
  · exact transStep_r0_5_eq k
  · exact transStep_r0_6_eq k
  · exact transStep_r0_7_eq k
  · exact transStep_r0_8_eq k
  · exact transStep_r0_9_eq k
  · exact transStep_r0_10_eq k
  · exact transStep_r0_11_eq k
  · exact transStep_r0_12_eq k
  · exact transStep_r0_13_eq k
  · exact transStep_r0_14_eq k
  · exact transStep_r0_15_eq k
lemma transStep_r1_0_eq : ∀ k : Fin 16, transStepExpr 1 0 k = transStep_r1_0 k := by decide +kernel
lemma transStep_r1_1_eq : ∀ k : Fin 16, transStepExpr 1 1 k = transStep_r1_1 k := by decide +kernel
lemma transStep_r1_2_eq : ∀ k : Fin 16, transStepExpr 1 2 k = transStep_r1_2 k := by decide +kernel
lemma transStep_r1_3_eq : ∀ k : Fin 16, transStepExpr 1 3 k = transStep_r1_3 k := by decide +kernel
lemma transStep_r1_4_eq : ∀ k : Fin 16, transStepExpr 1 4 k = transStep_r1_4 k := by decide +kernel
lemma transStep_r1_5_eq : ∀ k : Fin 16, transStepExpr 1 5 k = transStep_r1_5 k := by decide +kernel
lemma transStep_r1_6_eq : ∀ k : Fin 16, transStepExpr 1 6 k = transStep_r1_6 k := by decide +kernel
lemma transStep_r1_7_eq : ∀ k : Fin 16, transStepExpr 1 7 k = transStep_r1_7 k := by decide +kernel
lemma transStep_r1_8_eq : ∀ k : Fin 16, transStepExpr 1 8 k = transStep_r1_8 k := by decide +kernel
lemma transStep_r1_9_eq : ∀ k : Fin 16, transStepExpr 1 9 k = transStep_r1_9 k := by decide +kernel
lemma transStep_r1_10_eq : ∀ k : Fin 16, transStepExpr 1 10 k = transStep_r1_10 k := by decide +kernel
lemma transStep_r1_11_eq : ∀ k : Fin 16, transStepExpr 1 11 k = transStep_r1_11 k := by decide +kernel
lemma transStep_r1_12_eq : ∀ k : Fin 16, transStepExpr 1 12 k = transStep_r1_12 k := by decide +kernel
lemma transStep_r1_13_eq : ∀ k : Fin 16, transStepExpr 1 13 k = transStep_r1_13 k := by decide +kernel
lemma transStep_r1_14_eq : ∀ k : Fin 16, transStepExpr 1 14 k = transStep_r1_14 k := by decide +kernel
lemma transStep_r1_15_eq : ∀ k : Fin 16, transStepExpr 1 15 k = transStep_r1_15 k := by decide +kernel
lemma transStep_r1_eq (i k : Fin 16) : transStepExpr 1 i k = transStep_r1 i k := by
  fin_cases i
  · exact transStep_r1_0_eq k
  · exact transStep_r1_1_eq k
  · exact transStep_r1_2_eq k
  · exact transStep_r1_3_eq k
  · exact transStep_r1_4_eq k
  · exact transStep_r1_5_eq k
  · exact transStep_r1_6_eq k
  · exact transStep_r1_7_eq k
  · exact transStep_r1_8_eq k
  · exact transStep_r1_9_eq k
  · exact transStep_r1_10_eq k
  · exact transStep_r1_11_eq k
  · exact transStep_r1_12_eq k
  · exact transStep_r1_13_eq k
  · exact transStep_r1_14_eq k
  · exact transStep_r1_15_eq k
lemma transStep_r2_0_eq : ∀ k : Fin 16, transStepExpr 2 0 k = transStep_r2_0 k := by decide +kernel
lemma transStep_r2_1_eq : ∀ k : Fin 16, transStepExpr 2 1 k = transStep_r2_1 k := by decide +kernel
lemma transStep_r2_2_eq : ∀ k : Fin 16, transStepExpr 2 2 k = transStep_r2_2 k := by decide +kernel
lemma transStep_r2_3_eq : ∀ k : Fin 16, transStepExpr 2 3 k = transStep_r2_3 k := by decide +kernel
lemma transStep_r2_4_eq : ∀ k : Fin 16, transStepExpr 2 4 k = transStep_r2_4 k := by decide +kernel
lemma transStep_r2_5_eq : ∀ k : Fin 16, transStepExpr 2 5 k = transStep_r2_5 k := by decide +kernel
lemma transStep_r2_6_eq : ∀ k : Fin 16, transStepExpr 2 6 k = transStep_r2_6 k := by decide +kernel
lemma transStep_r2_7_eq : ∀ k : Fin 16, transStepExpr 2 7 k = transStep_r2_7 k := by decide +kernel
lemma transStep_r2_8_eq : ∀ k : Fin 16, transStepExpr 2 8 k = transStep_r2_8 k := by decide +kernel
lemma transStep_r2_9_eq : ∀ k : Fin 16, transStepExpr 2 9 k = transStep_r2_9 k := by decide +kernel
lemma transStep_r2_10_eq : ∀ k : Fin 16, transStepExpr 2 10 k = transStep_r2_10 k := by decide +kernel
lemma transStep_r2_11_eq : ∀ k : Fin 16, transStepExpr 2 11 k = transStep_r2_11 k := by decide +kernel
lemma transStep_r2_12_eq : ∀ k : Fin 16, transStepExpr 2 12 k = transStep_r2_12 k := by decide +kernel
lemma transStep_r2_13_eq : ∀ k : Fin 16, transStepExpr 2 13 k = transStep_r2_13 k := by decide +kernel
lemma transStep_r2_14_eq : ∀ k : Fin 16, transStepExpr 2 14 k = transStep_r2_14 k := by decide +kernel
lemma transStep_r2_15_eq : ∀ k : Fin 16, transStepExpr 2 15 k = transStep_r2_15 k := by decide +kernel
lemma transStep_r2_eq (i k : Fin 16) : transStepExpr 2 i k = transStep_r2 i k := by
  fin_cases i
  · exact transStep_r2_0_eq k
  · exact transStep_r2_1_eq k
  · exact transStep_r2_2_eq k
  · exact transStep_r2_3_eq k
  · exact transStep_r2_4_eq k
  · exact transStep_r2_5_eq k
  · exact transStep_r2_6_eq k
  · exact transStep_r2_7_eq k
  · exact transStep_r2_8_eq k
  · exact transStep_r2_9_eq k
  · exact transStep_r2_10_eq k
  · exact transStep_r2_11_eq k
  · exact transStep_r2_12_eq k
  · exact transStep_r2_13_eq k
  · exact transStep_r2_14_eq k
  · exact transStep_r2_15_eq k
lemma transStep_r3_0_eq : ∀ k : Fin 16, transStepExpr 3 0 k = transStep_r3_0 k := by decide +kernel
lemma transStep_r3_1_eq : ∀ k : Fin 16, transStepExpr 3 1 k = transStep_r3_1 k := by decide +kernel
lemma transStep_r3_2_eq : ∀ k : Fin 16, transStepExpr 3 2 k = transStep_r3_2 k := by decide +kernel
lemma transStep_r3_3_eq : ∀ k : Fin 16, transStepExpr 3 3 k = transStep_r3_3 k := by decide +kernel
lemma transStep_r3_4_eq : ∀ k : Fin 16, transStepExpr 3 4 k = transStep_r3_4 k := by decide +kernel
lemma transStep_r3_5_eq : ∀ k : Fin 16, transStepExpr 3 5 k = transStep_r3_5 k := by decide +kernel
lemma transStep_r3_6_eq : ∀ k : Fin 16, transStepExpr 3 6 k = transStep_r3_6 k := by decide +kernel
lemma transStep_r3_7_eq : ∀ k : Fin 16, transStepExpr 3 7 k = transStep_r3_7 k := by decide +kernel
lemma transStep_r3_8_eq : ∀ k : Fin 16, transStepExpr 3 8 k = transStep_r3_8 k := by decide +kernel
lemma transStep_r3_9_eq : ∀ k : Fin 16, transStepExpr 3 9 k = transStep_r3_9 k := by decide +kernel
lemma transStep_r3_10_eq : ∀ k : Fin 16, transStepExpr 3 10 k = transStep_r3_10 k := by decide +kernel
lemma transStep_r3_11_eq : ∀ k : Fin 16, transStepExpr 3 11 k = transStep_r3_11 k := by decide +kernel
lemma transStep_r3_12_eq : ∀ k : Fin 16, transStepExpr 3 12 k = transStep_r3_12 k := by decide +kernel
lemma transStep_r3_13_eq : ∀ k : Fin 16, transStepExpr 3 13 k = transStep_r3_13 k := by decide +kernel
lemma transStep_r3_14_eq : ∀ k : Fin 16, transStepExpr 3 14 k = transStep_r3_14 k := by decide +kernel
lemma transStep_r3_15_eq : ∀ k : Fin 16, transStepExpr 3 15 k = transStep_r3_15 k := by decide +kernel
lemma transStep_r3_eq (i k : Fin 16) : transStepExpr 3 i k = transStep_r3 i k := by
  fin_cases i
  · exact transStep_r3_0_eq k
  · exact transStep_r3_1_eq k
  · exact transStep_r3_2_eq k
  · exact transStep_r3_3_eq k
  · exact transStep_r3_4_eq k
  · exact transStep_r3_5_eq k
  · exact transStep_r3_6_eq k
  · exact transStep_r3_7_eq k
  · exact transStep_r3_8_eq k
  · exact transStep_r3_9_eq k
  · exact transStep_r3_10_eq k
  · exact transStep_r3_11_eq k
  · exact transStep_r3_12_eq k
  · exact transStep_r3_13_eq k
  · exact transStep_r3_14_eq k
  · exact transStep_r3_15_eq k
lemma transStep_r4_0_eq : ∀ k : Fin 16, transStepExpr 4 0 k = transStep_r4_0 k := by decide +kernel
lemma transStep_r4_1_eq : ∀ k : Fin 16, transStepExpr 4 1 k = transStep_r4_1 k := by decide +kernel
lemma transStep_r4_2_eq : ∀ k : Fin 16, transStepExpr 4 2 k = transStep_r4_2 k := by decide +kernel
lemma transStep_r4_3_eq : ∀ k : Fin 16, transStepExpr 4 3 k = transStep_r4_3 k := by decide +kernel
lemma transStep_r4_4_eq : ∀ k : Fin 16, transStepExpr 4 4 k = transStep_r4_4 k := by decide +kernel
lemma transStep_r4_5_eq : ∀ k : Fin 16, transStepExpr 4 5 k = transStep_r4_5 k := by decide +kernel
lemma transStep_r4_6_eq : ∀ k : Fin 16, transStepExpr 4 6 k = transStep_r4_6 k := by decide +kernel
lemma transStep_r4_7_eq : ∀ k : Fin 16, transStepExpr 4 7 k = transStep_r4_7 k := by decide +kernel
lemma transStep_r4_8_eq : ∀ k : Fin 16, transStepExpr 4 8 k = transStep_r4_8 k := by decide +kernel
lemma transStep_r4_9_eq : ∀ k : Fin 16, transStepExpr 4 9 k = transStep_r4_9 k := by decide +kernel
lemma transStep_r4_10_eq : ∀ k : Fin 16, transStepExpr 4 10 k = transStep_r4_10 k := by decide +kernel
lemma transStep_r4_11_eq : ∀ k : Fin 16, transStepExpr 4 11 k = transStep_r4_11 k := by decide +kernel
lemma transStep_r4_12_eq : ∀ k : Fin 16, transStepExpr 4 12 k = transStep_r4_12 k := by decide +kernel
lemma transStep_r4_13_eq : ∀ k : Fin 16, transStepExpr 4 13 k = transStep_r4_13 k := by decide +kernel
lemma transStep_r4_14_eq : ∀ k : Fin 16, transStepExpr 4 14 k = transStep_r4_14 k := by decide +kernel
lemma transStep_r4_15_eq : ∀ k : Fin 16, transStepExpr 4 15 k = transStep_r4_15 k := by decide +kernel
lemma transStep_r4_eq (i k : Fin 16) : transStepExpr 4 i k = transStep_r4 i k := by
  fin_cases i
  · exact transStep_r4_0_eq k
  · exact transStep_r4_1_eq k
  · exact transStep_r4_2_eq k
  · exact transStep_r4_3_eq k
  · exact transStep_r4_4_eq k
  · exact transStep_r4_5_eq k
  · exact transStep_r4_6_eq k
  · exact transStep_r4_7_eq k
  · exact transStep_r4_8_eq k
  · exact transStep_r4_9_eq k
  · exact transStep_r4_10_eq k
  · exact transStep_r4_11_eq k
  · exact transStep_r4_12_eq k
  · exact transStep_r4_13_eq k
  · exact transStep_r4_14_eq k
  · exact transStep_r4_15_eq k
lemma transStep_r5_0_eq : ∀ k : Fin 16, transStepExpr 5 0 k = transStep_r5_0 k := by decide +kernel
lemma transStep_r5_1_eq : ∀ k : Fin 16, transStepExpr 5 1 k = transStep_r5_1 k := by decide +kernel
lemma transStep_r5_2_eq : ∀ k : Fin 16, transStepExpr 5 2 k = transStep_r5_2 k := by decide +kernel
lemma transStep_r5_3_eq : ∀ k : Fin 16, transStepExpr 5 3 k = transStep_r5_3 k := by decide +kernel
lemma transStep_r5_4_eq : ∀ k : Fin 16, transStepExpr 5 4 k = transStep_r5_4 k := by decide +kernel
lemma transStep_r5_5_eq : ∀ k : Fin 16, transStepExpr 5 5 k = transStep_r5_5 k := by decide +kernel
lemma transStep_r5_6_eq : ∀ k : Fin 16, transStepExpr 5 6 k = transStep_r5_6 k := by decide +kernel
lemma transStep_r5_7_eq : ∀ k : Fin 16, transStepExpr 5 7 k = transStep_r5_7 k := by decide +kernel
lemma transStep_r5_8_eq : ∀ k : Fin 16, transStepExpr 5 8 k = transStep_r5_8 k := by decide +kernel
lemma transStep_r5_9_eq : ∀ k : Fin 16, transStepExpr 5 9 k = transStep_r5_9 k := by decide +kernel
lemma transStep_r5_10_eq : ∀ k : Fin 16, transStepExpr 5 10 k = transStep_r5_10 k := by decide +kernel
lemma transStep_r5_11_eq : ∀ k : Fin 16, transStepExpr 5 11 k = transStep_r5_11 k := by decide +kernel
lemma transStep_r5_12_eq : ∀ k : Fin 16, transStepExpr 5 12 k = transStep_r5_12 k := by decide +kernel
lemma transStep_r5_13_eq : ∀ k : Fin 16, transStepExpr 5 13 k = transStep_r5_13 k := by decide +kernel
lemma transStep_r5_14_eq : ∀ k : Fin 16, transStepExpr 5 14 k = transStep_r5_14 k := by decide +kernel
lemma transStep_r5_15_eq : ∀ k : Fin 16, transStepExpr 5 15 k = transStep_r5_15 k := by decide +kernel
lemma transStep_r5_eq (i k : Fin 16) : transStepExpr 5 i k = transStep_r5 i k := by
  fin_cases i
  · exact transStep_r5_0_eq k
  · exact transStep_r5_1_eq k
  · exact transStep_r5_2_eq k
  · exact transStep_r5_3_eq k
  · exact transStep_r5_4_eq k
  · exact transStep_r5_5_eq k
  · exact transStep_r5_6_eq k
  · exact transStep_r5_7_eq k
  · exact transStep_r5_8_eq k
  · exact transStep_r5_9_eq k
  · exact transStep_r5_10_eq k
  · exact transStep_r5_11_eq k
  · exact transStep_r5_12_eq k
  · exact transStep_r5_13_eq k
  · exact transStep_r5_14_eq k
  · exact transStep_r5_15_eq k
lemma transStep_eq (j : Fin 6) (i k : Fin 16) : transStepExpr j i k = transStep j i k := by
  fin_cases j
  · exact transStep_r0_eq i k
  · exact transStep_r1_eq i k
  · exact transStep_r2_eq i k
  · exact transStep_r3_eq i k
  · exact transStep_r4_eq i k
  · exact transStep_r5_eq i k
lemma transStep_contains (j : Fin 6) (i k : Fin 16) :
    (transStep j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)))) := by
  rw [← transStep_eq]
  exact transformedStepBox_contains (gridRows_contains_g j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers100
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
lemma trans92_r0_0_eq : ∀ k : Fin 16, trans92Expr 0 0 k = trans92_r0_0 k := by decide +kernel
lemma trans92_r0_1_eq : ∀ k : Fin 16, trans92Expr 0 1 k = trans92_r0_1 k := by decide +kernel
lemma trans92_r0_2_eq : ∀ k : Fin 16, trans92Expr 0 2 k = trans92_r0_2 k := by decide +kernel
lemma trans92_r0_3_eq : ∀ k : Fin 16, trans92Expr 0 3 k = trans92_r0_3 k := by decide +kernel
lemma trans92_r0_4_eq : ∀ k : Fin 16, trans92Expr 0 4 k = trans92_r0_4 k := by decide +kernel
lemma trans92_r0_5_eq : ∀ k : Fin 16, trans92Expr 0 5 k = trans92_r0_5 k := by decide +kernel
lemma trans92_r0_6_eq : ∀ k : Fin 16, trans92Expr 0 6 k = trans92_r0_6 k := by decide +kernel
lemma trans92_r0_7_eq : ∀ k : Fin 16, trans92Expr 0 7 k = trans92_r0_7 k := by decide +kernel
lemma trans92_r0_8_eq : ∀ k : Fin 16, trans92Expr 0 8 k = trans92_r0_8 k := by decide +kernel
lemma trans92_r0_9_eq : ∀ k : Fin 16, trans92Expr 0 9 k = trans92_r0_9 k := by decide +kernel
lemma trans92_r0_10_eq : ∀ k : Fin 16, trans92Expr 0 10 k = trans92_r0_10 k := by decide +kernel
lemma trans92_r0_11_eq : ∀ k : Fin 16, trans92Expr 0 11 k = trans92_r0_11 k := by decide +kernel
lemma trans92_r0_12_eq : ∀ k : Fin 16, trans92Expr 0 12 k = trans92_r0_12 k := by decide +kernel
lemma trans92_r0_13_eq : ∀ k : Fin 16, trans92Expr 0 13 k = trans92_r0_13 k := by decide +kernel
lemma trans92_r0_14_eq : ∀ k : Fin 16, trans92Expr 0 14 k = trans92_r0_14 k := by decide +kernel
lemma trans92_r0_15_eq : ∀ k : Fin 16, trans92Expr 0 15 k = trans92_r0_15 k := by decide +kernel
lemma trans92_r0_eq (i k : Fin 16) : trans92Expr 0 i k = trans92_r0 i k := by
  fin_cases i
  · exact trans92_r0_0_eq k
  · exact trans92_r0_1_eq k
  · exact trans92_r0_2_eq k
  · exact trans92_r0_3_eq k
  · exact trans92_r0_4_eq k
  · exact trans92_r0_5_eq k
  · exact trans92_r0_6_eq k
  · exact trans92_r0_7_eq k
  · exact trans92_r0_8_eq k
  · exact trans92_r0_9_eq k
  · exact trans92_r0_10_eq k
  · exact trans92_r0_11_eq k
  · exact trans92_r0_12_eq k
  · exact trans92_r0_13_eq k
  · exact trans92_r0_14_eq k
  · exact trans92_r0_15_eq k
lemma trans92_r1_0_eq : ∀ k : Fin 16, trans92Expr 1 0 k = trans92_r1_0 k := by decide +kernel
lemma trans92_r1_1_eq : ∀ k : Fin 16, trans92Expr 1 1 k = trans92_r1_1 k := by decide +kernel
lemma trans92_r1_2_eq : ∀ k : Fin 16, trans92Expr 1 2 k = trans92_r1_2 k := by decide +kernel
lemma trans92_r1_3_eq : ∀ k : Fin 16, trans92Expr 1 3 k = trans92_r1_3 k := by decide +kernel
lemma trans92_r1_4_eq : ∀ k : Fin 16, trans92Expr 1 4 k = trans92_r1_4 k := by decide +kernel
lemma trans92_r1_5_eq : ∀ k : Fin 16, trans92Expr 1 5 k = trans92_r1_5 k := by decide +kernel
lemma trans92_r1_6_eq : ∀ k : Fin 16, trans92Expr 1 6 k = trans92_r1_6 k := by decide +kernel
lemma trans92_r1_7_eq : ∀ k : Fin 16, trans92Expr 1 7 k = trans92_r1_7 k := by decide +kernel
lemma trans92_r1_8_eq : ∀ k : Fin 16, trans92Expr 1 8 k = trans92_r1_8 k := by decide +kernel
lemma trans92_r1_9_eq : ∀ k : Fin 16, trans92Expr 1 9 k = trans92_r1_9 k := by decide +kernel
lemma trans92_r1_10_eq : ∀ k : Fin 16, trans92Expr 1 10 k = trans92_r1_10 k := by decide +kernel
lemma trans92_r1_11_eq : ∀ k : Fin 16, trans92Expr 1 11 k = trans92_r1_11 k := by decide +kernel
lemma trans92_r1_12_eq : ∀ k : Fin 16, trans92Expr 1 12 k = trans92_r1_12 k := by decide +kernel
lemma trans92_r1_13_eq : ∀ k : Fin 16, trans92Expr 1 13 k = trans92_r1_13 k := by decide +kernel
lemma trans92_r1_14_eq : ∀ k : Fin 16, trans92Expr 1 14 k = trans92_r1_14 k := by decide +kernel
lemma trans92_r1_15_eq : ∀ k : Fin 16, trans92Expr 1 15 k = trans92_r1_15 k := by decide +kernel
lemma trans92_r1_eq (i k : Fin 16) : trans92Expr 1 i k = trans92_r1 i k := by
  fin_cases i
  · exact trans92_r1_0_eq k
  · exact trans92_r1_1_eq k
  · exact trans92_r1_2_eq k
  · exact trans92_r1_3_eq k
  · exact trans92_r1_4_eq k
  · exact trans92_r1_5_eq k
  · exact trans92_r1_6_eq k
  · exact trans92_r1_7_eq k
  · exact trans92_r1_8_eq k
  · exact trans92_r1_9_eq k
  · exact trans92_r1_10_eq k
  · exact trans92_r1_11_eq k
  · exact trans92_r1_12_eq k
  · exact trans92_r1_13_eq k
  · exact trans92_r1_14_eq k
  · exact trans92_r1_15_eq k
lemma trans92_r2_0_eq : ∀ k : Fin 16, trans92Expr 2 0 k = trans92_r2_0 k := by decide +kernel
lemma trans92_r2_1_eq : ∀ k : Fin 16, trans92Expr 2 1 k = trans92_r2_1 k := by decide +kernel
lemma trans92_r2_2_eq : ∀ k : Fin 16, trans92Expr 2 2 k = trans92_r2_2 k := by decide +kernel
lemma trans92_r2_3_eq : ∀ k : Fin 16, trans92Expr 2 3 k = trans92_r2_3 k := by decide +kernel
lemma trans92_r2_4_eq : ∀ k : Fin 16, trans92Expr 2 4 k = trans92_r2_4 k := by decide +kernel
lemma trans92_r2_5_eq : ∀ k : Fin 16, trans92Expr 2 5 k = trans92_r2_5 k := by decide +kernel
lemma trans92_r2_6_eq : ∀ k : Fin 16, trans92Expr 2 6 k = trans92_r2_6 k := by decide +kernel
lemma trans92_r2_7_eq : ∀ k : Fin 16, trans92Expr 2 7 k = trans92_r2_7 k := by decide +kernel
lemma trans92_r2_8_eq : ∀ k : Fin 16, trans92Expr 2 8 k = trans92_r2_8 k := by decide +kernel
lemma trans92_r2_9_eq : ∀ k : Fin 16, trans92Expr 2 9 k = trans92_r2_9 k := by decide +kernel
lemma trans92_r2_10_eq : ∀ k : Fin 16, trans92Expr 2 10 k = trans92_r2_10 k := by decide +kernel
lemma trans92_r2_11_eq : ∀ k : Fin 16, trans92Expr 2 11 k = trans92_r2_11 k := by decide +kernel
lemma trans92_r2_12_eq : ∀ k : Fin 16, trans92Expr 2 12 k = trans92_r2_12 k := by decide +kernel
lemma trans92_r2_13_eq : ∀ k : Fin 16, trans92Expr 2 13 k = trans92_r2_13 k := by decide +kernel
lemma trans92_r2_14_eq : ∀ k : Fin 16, trans92Expr 2 14 k = trans92_r2_14 k := by decide +kernel
lemma trans92_r2_15_eq : ∀ k : Fin 16, trans92Expr 2 15 k = trans92_r2_15 k := by decide +kernel
lemma trans92_r2_eq (i k : Fin 16) : trans92Expr 2 i k = trans92_r2 i k := by
  fin_cases i
  · exact trans92_r2_0_eq k
  · exact trans92_r2_1_eq k
  · exact trans92_r2_2_eq k
  · exact trans92_r2_3_eq k
  · exact trans92_r2_4_eq k
  · exact trans92_r2_5_eq k
  · exact trans92_r2_6_eq k
  · exact trans92_r2_7_eq k
  · exact trans92_r2_8_eq k
  · exact trans92_r2_9_eq k
  · exact trans92_r2_10_eq k
  · exact trans92_r2_11_eq k
  · exact trans92_r2_12_eq k
  · exact trans92_r2_13_eq k
  · exact trans92_r2_14_eq k
  · exact trans92_r2_15_eq k
lemma trans92_r3_0_eq : ∀ k : Fin 16, trans92Expr 3 0 k = trans92_r3_0 k := by decide +kernel
lemma trans92_r3_1_eq : ∀ k : Fin 16, trans92Expr 3 1 k = trans92_r3_1 k := by decide +kernel
lemma trans92_r3_2_eq : ∀ k : Fin 16, trans92Expr 3 2 k = trans92_r3_2 k := by decide +kernel
lemma trans92_r3_3_eq : ∀ k : Fin 16, trans92Expr 3 3 k = trans92_r3_3 k := by decide +kernel
lemma trans92_r3_4_eq : ∀ k : Fin 16, trans92Expr 3 4 k = trans92_r3_4 k := by decide +kernel
lemma trans92_r3_5_eq : ∀ k : Fin 16, trans92Expr 3 5 k = trans92_r3_5 k := by decide +kernel
lemma trans92_r3_6_eq : ∀ k : Fin 16, trans92Expr 3 6 k = trans92_r3_6 k := by decide +kernel
lemma trans92_r3_7_eq : ∀ k : Fin 16, trans92Expr 3 7 k = trans92_r3_7 k := by decide +kernel
lemma trans92_r3_8_eq : ∀ k : Fin 16, trans92Expr 3 8 k = trans92_r3_8 k := by decide +kernel
lemma trans92_r3_9_eq : ∀ k : Fin 16, trans92Expr 3 9 k = trans92_r3_9 k := by decide +kernel
lemma trans92_r3_10_eq : ∀ k : Fin 16, trans92Expr 3 10 k = trans92_r3_10 k := by decide +kernel
lemma trans92_r3_11_eq : ∀ k : Fin 16, trans92Expr 3 11 k = trans92_r3_11 k := by decide +kernel
lemma trans92_r3_12_eq : ∀ k : Fin 16, trans92Expr 3 12 k = trans92_r3_12 k := by decide +kernel
lemma trans92_r3_13_eq : ∀ k : Fin 16, trans92Expr 3 13 k = trans92_r3_13 k := by decide +kernel
lemma trans92_r3_14_eq : ∀ k : Fin 16, trans92Expr 3 14 k = trans92_r3_14 k := by decide +kernel
lemma trans92_r3_15_eq : ∀ k : Fin 16, trans92Expr 3 15 k = trans92_r3_15 k := by decide +kernel
lemma trans92_r3_eq (i k : Fin 16) : trans92Expr 3 i k = trans92_r3 i k := by
  fin_cases i
  · exact trans92_r3_0_eq k
  · exact trans92_r3_1_eq k
  · exact trans92_r3_2_eq k
  · exact trans92_r3_3_eq k
  · exact trans92_r3_4_eq k
  · exact trans92_r3_5_eq k
  · exact trans92_r3_6_eq k
  · exact trans92_r3_7_eq k
  · exact trans92_r3_8_eq k
  · exact trans92_r3_9_eq k
  · exact trans92_r3_10_eq k
  · exact trans92_r3_11_eq k
  · exact trans92_r3_12_eq k
  · exact trans92_r3_13_eq k
  · exact trans92_r3_14_eq k
  · exact trans92_r3_15_eq k
lemma trans92_r4_0_eq : ∀ k : Fin 16, trans92Expr 4 0 k = trans92_r4_0 k := by decide +kernel
lemma trans92_r4_1_eq : ∀ k : Fin 16, trans92Expr 4 1 k = trans92_r4_1 k := by decide +kernel
lemma trans92_r4_2_eq : ∀ k : Fin 16, trans92Expr 4 2 k = trans92_r4_2 k := by decide +kernel
lemma trans92_r4_3_eq : ∀ k : Fin 16, trans92Expr 4 3 k = trans92_r4_3 k := by decide +kernel
lemma trans92_r4_4_eq : ∀ k : Fin 16, trans92Expr 4 4 k = trans92_r4_4 k := by decide +kernel
lemma trans92_r4_5_eq : ∀ k : Fin 16, trans92Expr 4 5 k = trans92_r4_5 k := by decide +kernel
lemma trans92_r4_6_eq : ∀ k : Fin 16, trans92Expr 4 6 k = trans92_r4_6 k := by decide +kernel
lemma trans92_r4_7_eq : ∀ k : Fin 16, trans92Expr 4 7 k = trans92_r4_7 k := by decide +kernel
lemma trans92_r4_8_eq : ∀ k : Fin 16, trans92Expr 4 8 k = trans92_r4_8 k := by decide +kernel
lemma trans92_r4_9_eq : ∀ k : Fin 16, trans92Expr 4 9 k = trans92_r4_9 k := by decide +kernel
lemma trans92_r4_10_eq : ∀ k : Fin 16, trans92Expr 4 10 k = trans92_r4_10 k := by decide +kernel
lemma trans92_r4_11_eq : ∀ k : Fin 16, trans92Expr 4 11 k = trans92_r4_11 k := by decide +kernel
lemma trans92_r4_12_eq : ∀ k : Fin 16, trans92Expr 4 12 k = trans92_r4_12 k := by decide +kernel
lemma trans92_r4_13_eq : ∀ k : Fin 16, trans92Expr 4 13 k = trans92_r4_13 k := by decide +kernel
lemma trans92_r4_14_eq : ∀ k : Fin 16, trans92Expr 4 14 k = trans92_r4_14 k := by decide +kernel
lemma trans92_r4_15_eq : ∀ k : Fin 16, trans92Expr 4 15 k = trans92_r4_15 k := by decide +kernel
lemma trans92_r4_eq (i k : Fin 16) : trans92Expr 4 i k = trans92_r4 i k := by
  fin_cases i
  · exact trans92_r4_0_eq k
  · exact trans92_r4_1_eq k
  · exact trans92_r4_2_eq k
  · exact trans92_r4_3_eq k
  · exact trans92_r4_4_eq k
  · exact trans92_r4_5_eq k
  · exact trans92_r4_6_eq k
  · exact trans92_r4_7_eq k
  · exact trans92_r4_8_eq k
  · exact trans92_r4_9_eq k
  · exact trans92_r4_10_eq k
  · exact trans92_r4_11_eq k
  · exact trans92_r4_12_eq k
  · exact trans92_r4_13_eq k
  · exact trans92_r4_14_eq k
  · exact trans92_r4_15_eq k
lemma trans92_r5_0_eq : ∀ k : Fin 16, trans92Expr 5 0 k = trans92_r5_0 k := by decide +kernel
lemma trans92_r5_1_eq : ∀ k : Fin 16, trans92Expr 5 1 k = trans92_r5_1 k := by decide +kernel
lemma trans92_r5_2_eq : ∀ k : Fin 16, trans92Expr 5 2 k = trans92_r5_2 k := by decide +kernel
lemma trans92_r5_3_eq : ∀ k : Fin 16, trans92Expr 5 3 k = trans92_r5_3 k := by decide +kernel
lemma trans92_r5_4_eq : ∀ k : Fin 16, trans92Expr 5 4 k = trans92_r5_4 k := by decide +kernel
lemma trans92_r5_5_eq : ∀ k : Fin 16, trans92Expr 5 5 k = trans92_r5_5 k := by decide +kernel
lemma trans92_r5_6_eq : ∀ k : Fin 16, trans92Expr 5 6 k = trans92_r5_6 k := by decide +kernel
lemma trans92_r5_7_eq : ∀ k : Fin 16, trans92Expr 5 7 k = trans92_r5_7 k := by decide +kernel
lemma trans92_r5_8_eq : ∀ k : Fin 16, trans92Expr 5 8 k = trans92_r5_8 k := by decide +kernel
lemma trans92_r5_9_eq : ∀ k : Fin 16, trans92Expr 5 9 k = trans92_r5_9 k := by decide +kernel
lemma trans92_r5_10_eq : ∀ k : Fin 16, trans92Expr 5 10 k = trans92_r5_10 k := by decide +kernel
lemma trans92_r5_11_eq : ∀ k : Fin 16, trans92Expr 5 11 k = trans92_r5_11 k := by decide +kernel
lemma trans92_r5_12_eq : ∀ k : Fin 16, trans92Expr 5 12 k = trans92_r5_12 k := by decide +kernel
lemma trans92_r5_13_eq : ∀ k : Fin 16, trans92Expr 5 13 k = trans92_r5_13 k := by decide +kernel
lemma trans92_r5_14_eq : ∀ k : Fin 16, trans92Expr 5 14 k = trans92_r5_14 k := by decide +kernel
lemma trans92_r5_15_eq : ∀ k : Fin 16, trans92Expr 5 15 k = trans92_r5_15 k := by decide +kernel
lemma trans92_r5_eq (i k : Fin 16) : trans92Expr 5 i k = trans92_r5 i k := by
  fin_cases i
  · exact trans92_r5_0_eq k
  · exact trans92_r5_1_eq k
  · exact trans92_r5_2_eq k
  · exact trans92_r5_3_eq k
  · exact trans92_r5_4_eq k
  · exact trans92_r5_5_eq k
  · exact trans92_r5_6_eq k
  · exact trans92_r5_7_eq k
  · exact trans92_r5_8_eq k
  · exact trans92_r5_9_eq k
  · exact trans92_r5_10_eq k
  · exact trans92_r5_11_eq k
  · exact trans92_r5_12_eq k
  · exact trans92_r5_13_eq k
  · exact trans92_r5_14_eq k
  · exact trans92_r5_15_eq k
lemma trans92_eq (j : Fin 6) (i k : Fin 16) : trans92Expr j i k = trans92 j i k := by
  fin_cases j
  · exact trans92_r0_eq i k
  · exact trans92_r1_eq i k
  · exact trans92_r2_eq i k
  · exact trans92_r3_eq i k
  · exact trans92_r4_eq i k
  · exact trans92_r5_eq i k
lemma trans92_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (trans92 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(92:ℕ))) := by
  rw [← trans92_eq]
  unfold trans92Expr
  convert exp_transformed_step (trans91_contains_g j i k) (transStep_contains j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.trans92_contains_g_oai := @OAI.SharpPlanar.CachedData.trans92_contains_g_oai
