-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.kernel3_0_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:30:14.898383+00:00
-- url     : https://prove2.me/submissions/01117443-9af9-464b-bc03-7e1ef0577c37

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r0_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r1_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r2_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r3_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r4_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_10_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_11_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_12_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_13_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_14_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_15_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_1_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_2_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_3_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_4_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_5_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_6_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_7_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_8_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_r5_9_eq_e
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma pointLambda_eq (t : ℝ) : pointLambda t = lambda t := by
  unfold pointLambda lambda b h
  push_cast
  rfl
lemma pointZ_eq (t : ℝ) : pointZ t = z t := by
  unfold pointZ z B h
  push_cast
  rfl

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_transformed_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (Complex.I*Real.pi*z t*n)))
    (hq : q.Contains (Complex.exp (Complex.I*Real.pi*z t))) :
    (p.mul q).Contains (Complex.exp (Complex.I*Real.pi*z t*(n+1))) := by
  have hh := CBox.contains_mul_e hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma transformedStepBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) :
    (transformedStepBox p).Contains (Complex.exp (Complex.I*Real.pi*z t)) := by
  have hh := CBox.contains_powFast_e hp.2.2.2.2 3 4 (by norm_num)
  rw [← Complex.exp_nat_mul] at hh
  change (p.quarter.powFast 3 4).Contains _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [pointZ_eq]
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
lemma transStep_r0_eq (i k : Fin 16) : transStepExpr 0 i k = transStep_r0 i k := by
  fin_cases i
  · exact transStep_r0_0_eq_e k
  · exact transStep_r0_1_eq_e k
  · exact transStep_r0_2_eq_e k
  · exact transStep_r0_3_eq_e k
  · exact transStep_r0_4_eq_e k
  · exact transStep_r0_5_eq_e k
  · exact transStep_r0_6_eq_e k
  · exact transStep_r0_7_eq_e k
  · exact transStep_r0_8_eq_e k
  · exact transStep_r0_9_eq_e k
  · exact transStep_r0_10_eq_e k
  · exact transStep_r0_11_eq_e k
  · exact transStep_r0_12_eq_e k
  · exact transStep_r0_13_eq_e k
  · exact transStep_r0_14_eq_e k
  · exact transStep_r0_15_eq_e k
lemma transStep_r1_eq (i k : Fin 16) : transStepExpr 1 i k = transStep_r1 i k := by
  fin_cases i
  · exact transStep_r1_0_eq_e k
  · exact transStep_r1_1_eq_e k
  · exact transStep_r1_2_eq_e k
  · exact transStep_r1_3_eq_e k
  · exact transStep_r1_4_eq_e k
  · exact transStep_r1_5_eq_e k
  · exact transStep_r1_6_eq_e k
  · exact transStep_r1_7_eq_e k
  · exact transStep_r1_8_eq_e k
  · exact transStep_r1_9_eq_e k
  · exact transStep_r1_10_eq_e k
  · exact transStep_r1_11_eq_e k
  · exact transStep_r1_12_eq_e k
  · exact transStep_r1_13_eq_e k
  · exact transStep_r1_14_eq_e k
  · exact transStep_r1_15_eq_e k
lemma transStep_r2_eq (i k : Fin 16) : transStepExpr 2 i k = transStep_r2 i k := by
  fin_cases i
  · exact transStep_r2_0_eq_e k
  · exact transStep_r2_1_eq_e k
  · exact transStep_r2_2_eq_e k
  · exact transStep_r2_3_eq_e k
  · exact transStep_r2_4_eq_e k
  · exact transStep_r2_5_eq_e k
  · exact transStep_r2_6_eq_e k
  · exact transStep_r2_7_eq_e k
  · exact transStep_r2_8_eq_e k
  · exact transStep_r2_9_eq_e k
  · exact transStep_r2_10_eq_e k
  · exact transStep_r2_11_eq_e k
  · exact transStep_r2_12_eq_e k
  · exact transStep_r2_13_eq_e k
  · exact transStep_r2_14_eq_e k
  · exact transStep_r2_15_eq_e k
lemma transStep_r3_eq (i k : Fin 16) : transStepExpr 3 i k = transStep_r3 i k := by
  fin_cases i
  · exact transStep_r3_0_eq_e k
  · exact transStep_r3_1_eq_e k
  · exact transStep_r3_2_eq_e k
  · exact transStep_r3_3_eq_e k
  · exact transStep_r3_4_eq_e k
  · exact transStep_r3_5_eq_e k
  · exact transStep_r3_6_eq_e k
  · exact transStep_r3_7_eq_e k
  · exact transStep_r3_8_eq_e k
  · exact transStep_r3_9_eq_e k
  · exact transStep_r3_10_eq_e k
  · exact transStep_r3_11_eq_e k
  · exact transStep_r3_12_eq_e k
  · exact transStep_r3_13_eq_e k
  · exact transStep_r3_14_eq_e k
  · exact transStep_r3_15_eq_e k
lemma transStep_r4_eq (i k : Fin 16) : transStepExpr 4 i k = transStep_r4 i k := by
  fin_cases i
  · exact transStep_r4_0_eq_e k
  · exact transStep_r4_1_eq_e k
  · exact transStep_r4_2_eq_e k
  · exact transStep_r4_3_eq_e k
  · exact transStep_r4_4_eq_e k
  · exact transStep_r4_5_eq_e k
  · exact transStep_r4_6_eq_e k
  · exact transStep_r4_7_eq_e k
  · exact transStep_r4_8_eq_e k
  · exact transStep_r4_9_eq_e k
  · exact transStep_r4_10_eq_e k
  · exact transStep_r4_11_eq_e k
  · exact transStep_r4_12_eq_e k
  · exact transStep_r4_13_eq_e k
  · exact transStep_r4_14_eq_e k
  · exact transStep_r4_15_eq_e k
lemma transStep_r5_eq (i k : Fin 16) : transStepExpr 5 i k = transStep_r5 i k := by
  fin_cases i
  · exact transStep_r5_0_eq_e k
  · exact transStep_r5_1_eq_e k
  · exact transStep_r5_2_eq_e k
  · exact transStep_r5_3_eq_e k
  · exact transStep_r5_4_eq_e k
  · exact transStep_r5_5_eq_e k
  · exact transStep_r5_6_eq_e k
  · exact transStep_r5_7_eq_e k
  · exact transStep_r5_8_eq_e k
  · exact transStep_r5_9_eq_e k
  · exact transStep_r5_10_eq_e k
  · exact transStep_r5_11_eq_e k
  · exact transStep_r5_12_eq_e k
  · exact transStep_r5_13_eq_e k
  · exact transStep_r5_14_eq_e k
  · exact transStep_r5_15_eq_e k
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
  exact transformedStepBox_contains (gridRows_contains_e j i k)
lemma trans0_contains (j : Fin 6) (i k : Fin 16) :
    (trans0 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(0:ℕ))) := by
  simpa only [trans0,Nat.cast_zero,mul_zero,Complex.exp_zero,Int.cast_one,one_div,inv_one,Int.cast_zero,zero_div,mul_zero,zero_mul,add_zero] using
    (CBox.contains_rat_e 1 1 0 1 (by norm_num) (by norm_num))
lemma trans1_r0_0_eq : ∀ k : Fin 16, trans1Expr 0 0 k = trans1_r0_0 k := by decide +kernel
lemma trans1_r0_1_eq : ∀ k : Fin 16, trans1Expr 0 1 k = trans1_r0_1 k := by decide +kernel
lemma trans1_r0_2_eq : ∀ k : Fin 16, trans1Expr 0 2 k = trans1_r0_2 k := by decide +kernel
lemma trans1_r0_3_eq : ∀ k : Fin 16, trans1Expr 0 3 k = trans1_r0_3 k := by decide +kernel
lemma trans1_r0_4_eq : ∀ k : Fin 16, trans1Expr 0 4 k = trans1_r0_4 k := by decide +kernel
lemma trans1_r0_5_eq : ∀ k : Fin 16, trans1Expr 0 5 k = trans1_r0_5 k := by decide +kernel
lemma trans1_r0_6_eq : ∀ k : Fin 16, trans1Expr 0 6 k = trans1_r0_6 k := by decide +kernel
lemma trans1_r0_7_eq : ∀ k : Fin 16, trans1Expr 0 7 k = trans1_r0_7 k := by decide +kernel
lemma trans1_r0_8_eq : ∀ k : Fin 16, trans1Expr 0 8 k = trans1_r0_8 k := by decide +kernel
lemma trans1_r0_9_eq : ∀ k : Fin 16, trans1Expr 0 9 k = trans1_r0_9 k := by decide +kernel
lemma trans1_r0_10_eq : ∀ k : Fin 16, trans1Expr 0 10 k = trans1_r0_10 k := by decide +kernel
lemma trans1_r0_11_eq : ∀ k : Fin 16, trans1Expr 0 11 k = trans1_r0_11 k := by decide +kernel
lemma trans1_r0_12_eq : ∀ k : Fin 16, trans1Expr 0 12 k = trans1_r0_12 k := by decide +kernel
lemma trans1_r0_13_eq : ∀ k : Fin 16, trans1Expr 0 13 k = trans1_r0_13 k := by decide +kernel
lemma trans1_r0_14_eq : ∀ k : Fin 16, trans1Expr 0 14 k = trans1_r0_14 k := by decide +kernel
lemma trans1_r0_15_eq : ∀ k : Fin 16, trans1Expr 0 15 k = trans1_r0_15 k := by decide +kernel
lemma trans1_r0_eq (i k : Fin 16) : trans1Expr 0 i k = trans1_r0 i k := by
  fin_cases i
  · exact trans1_r0_0_eq k
  · exact trans1_r0_1_eq k
  · exact trans1_r0_2_eq k
  · exact trans1_r0_3_eq k
  · exact trans1_r0_4_eq k
  · exact trans1_r0_5_eq k
  · exact trans1_r0_6_eq k
  · exact trans1_r0_7_eq k
  · exact trans1_r0_8_eq k
  · exact trans1_r0_9_eq k
  · exact trans1_r0_10_eq k
  · exact trans1_r0_11_eq k
  · exact trans1_r0_12_eq k
  · exact trans1_r0_13_eq k
  · exact trans1_r0_14_eq k
  · exact trans1_r0_15_eq k
lemma trans1_r1_0_eq : ∀ k : Fin 16, trans1Expr 1 0 k = trans1_r1_0 k := by decide +kernel
lemma trans1_r1_1_eq : ∀ k : Fin 16, trans1Expr 1 1 k = trans1_r1_1 k := by decide +kernel
lemma trans1_r1_2_eq : ∀ k : Fin 16, trans1Expr 1 2 k = trans1_r1_2 k := by decide +kernel
lemma trans1_r1_3_eq : ∀ k : Fin 16, trans1Expr 1 3 k = trans1_r1_3 k := by decide +kernel
lemma trans1_r1_4_eq : ∀ k : Fin 16, trans1Expr 1 4 k = trans1_r1_4 k := by decide +kernel
lemma trans1_r1_5_eq : ∀ k : Fin 16, trans1Expr 1 5 k = trans1_r1_5 k := by decide +kernel
lemma trans1_r1_6_eq : ∀ k : Fin 16, trans1Expr 1 6 k = trans1_r1_6 k := by decide +kernel
lemma trans1_r1_7_eq : ∀ k : Fin 16, trans1Expr 1 7 k = trans1_r1_7 k := by decide +kernel
lemma trans1_r1_8_eq : ∀ k : Fin 16, trans1Expr 1 8 k = trans1_r1_8 k := by decide +kernel
lemma trans1_r1_9_eq : ∀ k : Fin 16, trans1Expr 1 9 k = trans1_r1_9 k := by decide +kernel
lemma trans1_r1_10_eq : ∀ k : Fin 16, trans1Expr 1 10 k = trans1_r1_10 k := by decide +kernel
lemma trans1_r1_11_eq : ∀ k : Fin 16, trans1Expr 1 11 k = trans1_r1_11 k := by decide +kernel
lemma trans1_r1_12_eq : ∀ k : Fin 16, trans1Expr 1 12 k = trans1_r1_12 k := by decide +kernel
lemma trans1_r1_13_eq : ∀ k : Fin 16, trans1Expr 1 13 k = trans1_r1_13 k := by decide +kernel
lemma trans1_r1_14_eq : ∀ k : Fin 16, trans1Expr 1 14 k = trans1_r1_14 k := by decide +kernel
lemma trans1_r1_15_eq : ∀ k : Fin 16, trans1Expr 1 15 k = trans1_r1_15 k := by decide +kernel
lemma trans1_r1_eq (i k : Fin 16) : trans1Expr 1 i k = trans1_r1 i k := by
  fin_cases i
  · exact trans1_r1_0_eq k
  · exact trans1_r1_1_eq k
  · exact trans1_r1_2_eq k
  · exact trans1_r1_3_eq k
  · exact trans1_r1_4_eq k
  · exact trans1_r1_5_eq k
  · exact trans1_r1_6_eq k
  · exact trans1_r1_7_eq k
  · exact trans1_r1_8_eq k
  · exact trans1_r1_9_eq k
  · exact trans1_r1_10_eq k
  · exact trans1_r1_11_eq k
  · exact trans1_r1_12_eq k
  · exact trans1_r1_13_eq k
  · exact trans1_r1_14_eq k
  · exact trans1_r1_15_eq k
lemma trans1_r2_0_eq : ∀ k : Fin 16, trans1Expr 2 0 k = trans1_r2_0 k := by decide +kernel
lemma trans1_r2_1_eq : ∀ k : Fin 16, trans1Expr 2 1 k = trans1_r2_1 k := by decide +kernel
lemma trans1_r2_2_eq : ∀ k : Fin 16, trans1Expr 2 2 k = trans1_r2_2 k := by decide +kernel
lemma trans1_r2_3_eq : ∀ k : Fin 16, trans1Expr 2 3 k = trans1_r2_3 k := by decide +kernel
lemma trans1_r2_4_eq : ∀ k : Fin 16, trans1Expr 2 4 k = trans1_r2_4 k := by decide +kernel
lemma trans1_r2_5_eq : ∀ k : Fin 16, trans1Expr 2 5 k = trans1_r2_5 k := by decide +kernel
lemma trans1_r2_6_eq : ∀ k : Fin 16, trans1Expr 2 6 k = trans1_r2_6 k := by decide +kernel
lemma trans1_r2_7_eq : ∀ k : Fin 16, trans1Expr 2 7 k = trans1_r2_7 k := by decide +kernel
lemma trans1_r2_8_eq : ∀ k : Fin 16, trans1Expr 2 8 k = trans1_r2_8 k := by decide +kernel
lemma trans1_r2_9_eq : ∀ k : Fin 16, trans1Expr 2 9 k = trans1_r2_9 k := by decide +kernel
lemma trans1_r2_10_eq : ∀ k : Fin 16, trans1Expr 2 10 k = trans1_r2_10 k := by decide +kernel
lemma trans1_r2_11_eq : ∀ k : Fin 16, trans1Expr 2 11 k = trans1_r2_11 k := by decide +kernel
lemma trans1_r2_12_eq : ∀ k : Fin 16, trans1Expr 2 12 k = trans1_r2_12 k := by decide +kernel
lemma trans1_r2_13_eq : ∀ k : Fin 16, trans1Expr 2 13 k = trans1_r2_13 k := by decide +kernel
lemma trans1_r2_14_eq : ∀ k : Fin 16, trans1Expr 2 14 k = trans1_r2_14 k := by decide +kernel
lemma trans1_r2_15_eq : ∀ k : Fin 16, trans1Expr 2 15 k = trans1_r2_15 k := by decide +kernel
lemma trans1_r2_eq (i k : Fin 16) : trans1Expr 2 i k = trans1_r2 i k := by
  fin_cases i
  · exact trans1_r2_0_eq k
  · exact trans1_r2_1_eq k
  · exact trans1_r2_2_eq k
  · exact trans1_r2_3_eq k
  · exact trans1_r2_4_eq k
  · exact trans1_r2_5_eq k
  · exact trans1_r2_6_eq k
  · exact trans1_r2_7_eq k
  · exact trans1_r2_8_eq k
  · exact trans1_r2_9_eq k
  · exact trans1_r2_10_eq k
  · exact trans1_r2_11_eq k
  · exact trans1_r2_12_eq k
  · exact trans1_r2_13_eq k
  · exact trans1_r2_14_eq k
  · exact trans1_r2_15_eq k
lemma trans1_r3_0_eq : ∀ k : Fin 16, trans1Expr 3 0 k = trans1_r3_0 k := by decide +kernel
lemma trans1_r3_1_eq : ∀ k : Fin 16, trans1Expr 3 1 k = trans1_r3_1 k := by decide +kernel
lemma trans1_r3_2_eq : ∀ k : Fin 16, trans1Expr 3 2 k = trans1_r3_2 k := by decide +kernel
lemma trans1_r3_3_eq : ∀ k : Fin 16, trans1Expr 3 3 k = trans1_r3_3 k := by decide +kernel
lemma trans1_r3_4_eq : ∀ k : Fin 16, trans1Expr 3 4 k = trans1_r3_4 k := by decide +kernel
lemma trans1_r3_5_eq : ∀ k : Fin 16, trans1Expr 3 5 k = trans1_r3_5 k := by decide +kernel
lemma trans1_r3_6_eq : ∀ k : Fin 16, trans1Expr 3 6 k = trans1_r3_6 k := by decide +kernel
lemma trans1_r3_7_eq : ∀ k : Fin 16, trans1Expr 3 7 k = trans1_r3_7 k := by decide +kernel
lemma trans1_r3_8_eq : ∀ k : Fin 16, trans1Expr 3 8 k = trans1_r3_8 k := by decide +kernel
lemma trans1_r3_9_eq : ∀ k : Fin 16, trans1Expr 3 9 k = trans1_r3_9 k := by decide +kernel
lemma trans1_r3_10_eq : ∀ k : Fin 16, trans1Expr 3 10 k = trans1_r3_10 k := by decide +kernel
lemma trans1_r3_11_eq : ∀ k : Fin 16, trans1Expr 3 11 k = trans1_r3_11 k := by decide +kernel
lemma trans1_r3_12_eq : ∀ k : Fin 16, trans1Expr 3 12 k = trans1_r3_12 k := by decide +kernel
lemma trans1_r3_13_eq : ∀ k : Fin 16, trans1Expr 3 13 k = trans1_r3_13 k := by decide +kernel
lemma trans1_r3_14_eq : ∀ k : Fin 16, trans1Expr 3 14 k = trans1_r3_14 k := by decide +kernel
lemma trans1_r3_15_eq : ∀ k : Fin 16, trans1Expr 3 15 k = trans1_r3_15 k := by decide +kernel
lemma trans1_r3_eq (i k : Fin 16) : trans1Expr 3 i k = trans1_r3 i k := by
  fin_cases i
  · exact trans1_r3_0_eq k
  · exact trans1_r3_1_eq k
  · exact trans1_r3_2_eq k
  · exact trans1_r3_3_eq k
  · exact trans1_r3_4_eq k
  · exact trans1_r3_5_eq k
  · exact trans1_r3_6_eq k
  · exact trans1_r3_7_eq k
  · exact trans1_r3_8_eq k
  · exact trans1_r3_9_eq k
  · exact trans1_r3_10_eq k
  · exact trans1_r3_11_eq k
  · exact trans1_r3_12_eq k
  · exact trans1_r3_13_eq k
  · exact trans1_r3_14_eq k
  · exact trans1_r3_15_eq k
lemma trans1_r4_0_eq : ∀ k : Fin 16, trans1Expr 4 0 k = trans1_r4_0 k := by decide +kernel
lemma trans1_r4_1_eq : ∀ k : Fin 16, trans1Expr 4 1 k = trans1_r4_1 k := by decide +kernel
lemma trans1_r4_2_eq : ∀ k : Fin 16, trans1Expr 4 2 k = trans1_r4_2 k := by decide +kernel
lemma trans1_r4_3_eq : ∀ k : Fin 16, trans1Expr 4 3 k = trans1_r4_3 k := by decide +kernel
lemma trans1_r4_4_eq : ∀ k : Fin 16, trans1Expr 4 4 k = trans1_r4_4 k := by decide +kernel
lemma trans1_r4_5_eq : ∀ k : Fin 16, trans1Expr 4 5 k = trans1_r4_5 k := by decide +kernel
lemma trans1_r4_6_eq : ∀ k : Fin 16, trans1Expr 4 6 k = trans1_r4_6 k := by decide +kernel
lemma trans1_r4_7_eq : ∀ k : Fin 16, trans1Expr 4 7 k = trans1_r4_7 k := by decide +kernel
lemma trans1_r4_8_eq : ∀ k : Fin 16, trans1Expr 4 8 k = trans1_r4_8 k := by decide +kernel
lemma trans1_r4_9_eq : ∀ k : Fin 16, trans1Expr 4 9 k = trans1_r4_9 k := by decide +kernel
lemma trans1_r4_10_eq : ∀ k : Fin 16, trans1Expr 4 10 k = trans1_r4_10 k := by decide +kernel
lemma trans1_r4_11_eq : ∀ k : Fin 16, trans1Expr 4 11 k = trans1_r4_11 k := by decide +kernel
lemma trans1_r4_12_eq : ∀ k : Fin 16, trans1Expr 4 12 k = trans1_r4_12 k := by decide +kernel
lemma trans1_r4_13_eq : ∀ k : Fin 16, trans1Expr 4 13 k = trans1_r4_13 k := by decide +kernel
lemma trans1_r4_14_eq : ∀ k : Fin 16, trans1Expr 4 14 k = trans1_r4_14 k := by decide +kernel
lemma trans1_r4_15_eq : ∀ k : Fin 16, trans1Expr 4 15 k = trans1_r4_15 k := by decide +kernel
lemma trans1_r4_eq (i k : Fin 16) : trans1Expr 4 i k = trans1_r4 i k := by
  fin_cases i
  · exact trans1_r4_0_eq k
  · exact trans1_r4_1_eq k
  · exact trans1_r4_2_eq k
  · exact trans1_r4_3_eq k
  · exact trans1_r4_4_eq k
  · exact trans1_r4_5_eq k
  · exact trans1_r4_6_eq k
  · exact trans1_r4_7_eq k
  · exact trans1_r4_8_eq k
  · exact trans1_r4_9_eq k
  · exact trans1_r4_10_eq k
  · exact trans1_r4_11_eq k
  · exact trans1_r4_12_eq k
  · exact trans1_r4_13_eq k
  · exact trans1_r4_14_eq k
  · exact trans1_r4_15_eq k
lemma trans1_r5_0_eq : ∀ k : Fin 16, trans1Expr 5 0 k = trans1_r5_0 k := by decide +kernel
lemma trans1_r5_1_eq : ∀ k : Fin 16, trans1Expr 5 1 k = trans1_r5_1 k := by decide +kernel
lemma trans1_r5_2_eq : ∀ k : Fin 16, trans1Expr 5 2 k = trans1_r5_2 k := by decide +kernel
lemma trans1_r5_3_eq : ∀ k : Fin 16, trans1Expr 5 3 k = trans1_r5_3 k := by decide +kernel
lemma trans1_r5_4_eq : ∀ k : Fin 16, trans1Expr 5 4 k = trans1_r5_4 k := by decide +kernel
lemma trans1_r5_5_eq : ∀ k : Fin 16, trans1Expr 5 5 k = trans1_r5_5 k := by decide +kernel
lemma trans1_r5_6_eq : ∀ k : Fin 16, trans1Expr 5 6 k = trans1_r5_6 k := by decide +kernel
lemma trans1_r5_7_eq : ∀ k : Fin 16, trans1Expr 5 7 k = trans1_r5_7 k := by decide +kernel
lemma trans1_r5_8_eq : ∀ k : Fin 16, trans1Expr 5 8 k = trans1_r5_8 k := by decide +kernel
lemma trans1_r5_9_eq : ∀ k : Fin 16, trans1Expr 5 9 k = trans1_r5_9 k := by decide +kernel
lemma trans1_r5_10_eq : ∀ k : Fin 16, trans1Expr 5 10 k = trans1_r5_10 k := by decide +kernel
lemma trans1_r5_11_eq : ∀ k : Fin 16, trans1Expr 5 11 k = trans1_r5_11 k := by decide +kernel
lemma trans1_r5_12_eq : ∀ k : Fin 16, trans1Expr 5 12 k = trans1_r5_12 k := by decide +kernel
lemma trans1_r5_13_eq : ∀ k : Fin 16, trans1Expr 5 13 k = trans1_r5_13 k := by decide +kernel
lemma trans1_r5_14_eq : ∀ k : Fin 16, trans1Expr 5 14 k = trans1_r5_14 k := by decide +kernel
lemma trans1_r5_15_eq : ∀ k : Fin 16, trans1Expr 5 15 k = trans1_r5_15 k := by decide +kernel
lemma trans1_r5_eq (i k : Fin 16) : trans1Expr 5 i k = trans1_r5 i k := by
  fin_cases i
  · exact trans1_r5_0_eq k
  · exact trans1_r5_1_eq k
  · exact trans1_r5_2_eq k
  · exact trans1_r5_3_eq k
  · exact trans1_r5_4_eq k
  · exact trans1_r5_5_eq k
  · exact trans1_r5_6_eq k
  · exact trans1_r5_7_eq k
  · exact trans1_r5_8_eq k
  · exact trans1_r5_9_eq k
  · exact trans1_r5_10_eq k
  · exact trans1_r5_11_eq k
  · exact trans1_r5_12_eq k
  · exact trans1_r5_13_eq k
  · exact trans1_r5_14_eq k
  · exact trans1_r5_15_eq k
lemma trans1_eq (j : Fin 6) (i k : Fin 16) : trans1Expr j i k = trans1 j i k := by
  fin_cases j
  · exact trans1_r0_eq i k
  · exact trans1_r1_eq i k
  · exact trans1_r2_eq i k
  · exact trans1_r3_eq i k
  · exact trans1_r4_eq i k
  · exact trans1_r5_eq i k
lemma trans1_contains (j : Fin 6) (i k : Fin 16) :
    (trans1 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(1:ℕ))) := by
  rw [← trans1_eq]
  unfold trans1Expr
  convert exp_transformed_step (trans0_contains j i k) (transStep_contains j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
lemma trans2_r0_0_eq : ∀ k : Fin 16, trans2Expr 0 0 k = trans2_r0_0 k := by decide +kernel
lemma trans2_r0_1_eq : ∀ k : Fin 16, trans2Expr 0 1 k = trans2_r0_1 k := by decide +kernel
lemma trans2_r0_2_eq : ∀ k : Fin 16, trans2Expr 0 2 k = trans2_r0_2 k := by decide +kernel
lemma trans2_r0_3_eq : ∀ k : Fin 16, trans2Expr 0 3 k = trans2_r0_3 k := by decide +kernel
lemma trans2_r0_4_eq : ∀ k : Fin 16, trans2Expr 0 4 k = trans2_r0_4 k := by decide +kernel
lemma trans2_r0_5_eq : ∀ k : Fin 16, trans2Expr 0 5 k = trans2_r0_5 k := by decide +kernel
lemma trans2_r0_6_eq : ∀ k : Fin 16, trans2Expr 0 6 k = trans2_r0_6 k := by decide +kernel
lemma trans2_r0_7_eq : ∀ k : Fin 16, trans2Expr 0 7 k = trans2_r0_7 k := by decide +kernel
lemma trans2_r0_8_eq : ∀ k : Fin 16, trans2Expr 0 8 k = trans2_r0_8 k := by decide +kernel
lemma trans2_r0_9_eq : ∀ k : Fin 16, trans2Expr 0 9 k = trans2_r0_9 k := by decide +kernel
lemma trans2_r0_10_eq : ∀ k : Fin 16, trans2Expr 0 10 k = trans2_r0_10 k := by decide +kernel
lemma trans2_r0_11_eq : ∀ k : Fin 16, trans2Expr 0 11 k = trans2_r0_11 k := by decide +kernel
lemma trans2_r0_12_eq : ∀ k : Fin 16, trans2Expr 0 12 k = trans2_r0_12 k := by decide +kernel
lemma trans2_r0_13_eq : ∀ k : Fin 16, trans2Expr 0 13 k = trans2_r0_13 k := by decide +kernel
lemma trans2_r0_14_eq : ∀ k : Fin 16, trans2Expr 0 14 k = trans2_r0_14 k := by decide +kernel
lemma trans2_r0_15_eq : ∀ k : Fin 16, trans2Expr 0 15 k = trans2_r0_15 k := by decide +kernel
lemma trans2_r0_eq (i k : Fin 16) : trans2Expr 0 i k = trans2_r0 i k := by
  fin_cases i
  · exact trans2_r0_0_eq k
  · exact trans2_r0_1_eq k
  · exact trans2_r0_2_eq k
  · exact trans2_r0_3_eq k
  · exact trans2_r0_4_eq k
  · exact trans2_r0_5_eq k
  · exact trans2_r0_6_eq k
  · exact trans2_r0_7_eq k
  · exact trans2_r0_8_eq k
  · exact trans2_r0_9_eq k
  · exact trans2_r0_10_eq k
  · exact trans2_r0_11_eq k
  · exact trans2_r0_12_eq k
  · exact trans2_r0_13_eq k
  · exact trans2_r0_14_eq k
  · exact trans2_r0_15_eq k
lemma trans2_r1_0_eq : ∀ k : Fin 16, trans2Expr 1 0 k = trans2_r1_0 k := by decide +kernel
lemma trans2_r1_1_eq : ∀ k : Fin 16, trans2Expr 1 1 k = trans2_r1_1 k := by decide +kernel
lemma trans2_r1_2_eq : ∀ k : Fin 16, trans2Expr 1 2 k = trans2_r1_2 k := by decide +kernel
lemma trans2_r1_3_eq : ∀ k : Fin 16, trans2Expr 1 3 k = trans2_r1_3 k := by decide +kernel
lemma trans2_r1_4_eq : ∀ k : Fin 16, trans2Expr 1 4 k = trans2_r1_4 k := by decide +kernel
lemma trans2_r1_5_eq : ∀ k : Fin 16, trans2Expr 1 5 k = trans2_r1_5 k := by decide +kernel
lemma trans2_r1_6_eq : ∀ k : Fin 16, trans2Expr 1 6 k = trans2_r1_6 k := by decide +kernel
lemma trans2_r1_7_eq : ∀ k : Fin 16, trans2Expr 1 7 k = trans2_r1_7 k := by decide +kernel
lemma trans2_r1_8_eq : ∀ k : Fin 16, trans2Expr 1 8 k = trans2_r1_8 k := by decide +kernel
lemma trans2_r1_9_eq : ∀ k : Fin 16, trans2Expr 1 9 k = trans2_r1_9 k := by decide +kernel
lemma trans2_r1_10_eq : ∀ k : Fin 16, trans2Expr 1 10 k = trans2_r1_10 k := by decide +kernel
lemma trans2_r1_11_eq : ∀ k : Fin 16, trans2Expr 1 11 k = trans2_r1_11 k := by decide +kernel
lemma trans2_r1_12_eq : ∀ k : Fin 16, trans2Expr 1 12 k = trans2_r1_12 k := by decide +kernel
lemma trans2_r1_13_eq : ∀ k : Fin 16, trans2Expr 1 13 k = trans2_r1_13 k := by decide +kernel
lemma trans2_r1_14_eq : ∀ k : Fin 16, trans2Expr 1 14 k = trans2_r1_14 k := by decide +kernel
lemma trans2_r1_15_eq : ∀ k : Fin 16, trans2Expr 1 15 k = trans2_r1_15 k := by decide +kernel
lemma trans2_r1_eq (i k : Fin 16) : trans2Expr 1 i k = trans2_r1 i k := by
  fin_cases i
  · exact trans2_r1_0_eq k
  · exact trans2_r1_1_eq k
  · exact trans2_r1_2_eq k
  · exact trans2_r1_3_eq k
  · exact trans2_r1_4_eq k
  · exact trans2_r1_5_eq k
  · exact trans2_r1_6_eq k
  · exact trans2_r1_7_eq k
  · exact trans2_r1_8_eq k
  · exact trans2_r1_9_eq k
  · exact trans2_r1_10_eq k
  · exact trans2_r1_11_eq k
  · exact trans2_r1_12_eq k
  · exact trans2_r1_13_eq k
  · exact trans2_r1_14_eq k
  · exact trans2_r1_15_eq k
lemma trans2_r2_0_eq : ∀ k : Fin 16, trans2Expr 2 0 k = trans2_r2_0 k := by decide +kernel
lemma trans2_r2_1_eq : ∀ k : Fin 16, trans2Expr 2 1 k = trans2_r2_1 k := by decide +kernel
lemma trans2_r2_2_eq : ∀ k : Fin 16, trans2Expr 2 2 k = trans2_r2_2 k := by decide +kernel
lemma trans2_r2_3_eq : ∀ k : Fin 16, trans2Expr 2 3 k = trans2_r2_3 k := by decide +kernel
lemma trans2_r2_4_eq : ∀ k : Fin 16, trans2Expr 2 4 k = trans2_r2_4 k := by decide +kernel
lemma trans2_r2_5_eq : ∀ k : Fin 16, trans2Expr 2 5 k = trans2_r2_5 k := by decide +kernel
lemma trans2_r2_6_eq : ∀ k : Fin 16, trans2Expr 2 6 k = trans2_r2_6 k := by decide +kernel
lemma trans2_r2_7_eq : ∀ k : Fin 16, trans2Expr 2 7 k = trans2_r2_7 k := by decide +kernel
lemma trans2_r2_8_eq : ∀ k : Fin 16, trans2Expr 2 8 k = trans2_r2_8 k := by decide +kernel
lemma trans2_r2_9_eq : ∀ k : Fin 16, trans2Expr 2 9 k = trans2_r2_9 k := by decide +kernel
lemma trans2_r2_10_eq : ∀ k : Fin 16, trans2Expr 2 10 k = trans2_r2_10 k := by decide +kernel
lemma trans2_r2_11_eq : ∀ k : Fin 16, trans2Expr 2 11 k = trans2_r2_11 k := by decide +kernel
lemma trans2_r2_12_eq : ∀ k : Fin 16, trans2Expr 2 12 k = trans2_r2_12 k := by decide +kernel
lemma trans2_r2_13_eq : ∀ k : Fin 16, trans2Expr 2 13 k = trans2_r2_13 k := by decide +kernel
lemma trans2_r2_14_eq : ∀ k : Fin 16, trans2Expr 2 14 k = trans2_r2_14 k := by decide +kernel
lemma trans2_r2_15_eq : ∀ k : Fin 16, trans2Expr 2 15 k = trans2_r2_15 k := by decide +kernel
lemma trans2_r2_eq (i k : Fin 16) : trans2Expr 2 i k = trans2_r2 i k := by
  fin_cases i
  · exact trans2_r2_0_eq k
  · exact trans2_r2_1_eq k
  · exact trans2_r2_2_eq k
  · exact trans2_r2_3_eq k
  · exact trans2_r2_4_eq k
  · exact trans2_r2_5_eq k
  · exact trans2_r2_6_eq k
  · exact trans2_r2_7_eq k
  · exact trans2_r2_8_eq k
  · exact trans2_r2_9_eq k
  · exact trans2_r2_10_eq k
  · exact trans2_r2_11_eq k
  · exact trans2_r2_12_eq k
  · exact trans2_r2_13_eq k
  · exact trans2_r2_14_eq k
  · exact trans2_r2_15_eq k
lemma trans2_r3_0_eq : ∀ k : Fin 16, trans2Expr 3 0 k = trans2_r3_0 k := by decide +kernel
lemma trans2_r3_1_eq : ∀ k : Fin 16, trans2Expr 3 1 k = trans2_r3_1 k := by decide +kernel
lemma trans2_r3_2_eq : ∀ k : Fin 16, trans2Expr 3 2 k = trans2_r3_2 k := by decide +kernel
lemma trans2_r3_3_eq : ∀ k : Fin 16, trans2Expr 3 3 k = trans2_r3_3 k := by decide +kernel
lemma trans2_r3_4_eq : ∀ k : Fin 16, trans2Expr 3 4 k = trans2_r3_4 k := by decide +kernel
lemma trans2_r3_5_eq : ∀ k : Fin 16, trans2Expr 3 5 k = trans2_r3_5 k := by decide +kernel
lemma trans2_r3_6_eq : ∀ k : Fin 16, trans2Expr 3 6 k = trans2_r3_6 k := by decide +kernel
lemma trans2_r3_7_eq : ∀ k : Fin 16, trans2Expr 3 7 k = trans2_r3_7 k := by decide +kernel
lemma trans2_r3_8_eq : ∀ k : Fin 16, trans2Expr 3 8 k = trans2_r3_8 k := by decide +kernel
lemma trans2_r3_9_eq : ∀ k : Fin 16, trans2Expr 3 9 k = trans2_r3_9 k := by decide +kernel
lemma trans2_r3_10_eq : ∀ k : Fin 16, trans2Expr 3 10 k = trans2_r3_10 k := by decide +kernel
lemma trans2_r3_11_eq : ∀ k : Fin 16, trans2Expr 3 11 k = trans2_r3_11 k := by decide +kernel
lemma trans2_r3_12_eq : ∀ k : Fin 16, trans2Expr 3 12 k = trans2_r3_12 k := by decide +kernel
lemma trans2_r3_13_eq : ∀ k : Fin 16, trans2Expr 3 13 k = trans2_r3_13 k := by decide +kernel
lemma trans2_r3_14_eq : ∀ k : Fin 16, trans2Expr 3 14 k = trans2_r3_14 k := by decide +kernel
lemma trans2_r3_15_eq : ∀ k : Fin 16, trans2Expr 3 15 k = trans2_r3_15 k := by decide +kernel
lemma trans2_r3_eq (i k : Fin 16) : trans2Expr 3 i k = trans2_r3 i k := by
  fin_cases i
  · exact trans2_r3_0_eq k
  · exact trans2_r3_1_eq k
  · exact trans2_r3_2_eq k
  · exact trans2_r3_3_eq k
  · exact trans2_r3_4_eq k
  · exact trans2_r3_5_eq k
  · exact trans2_r3_6_eq k
  · exact trans2_r3_7_eq k
  · exact trans2_r3_8_eq k
  · exact trans2_r3_9_eq k
  · exact trans2_r3_10_eq k
  · exact trans2_r3_11_eq k
  · exact trans2_r3_12_eq k
  · exact trans2_r3_13_eq k
  · exact trans2_r3_14_eq k
  · exact trans2_r3_15_eq k
lemma trans2_r4_0_eq : ∀ k : Fin 16, trans2Expr 4 0 k = trans2_r4_0 k := by decide +kernel
lemma trans2_r4_1_eq : ∀ k : Fin 16, trans2Expr 4 1 k = trans2_r4_1 k := by decide +kernel
lemma trans2_r4_2_eq : ∀ k : Fin 16, trans2Expr 4 2 k = trans2_r4_2 k := by decide +kernel
lemma trans2_r4_3_eq : ∀ k : Fin 16, trans2Expr 4 3 k = trans2_r4_3 k := by decide +kernel
lemma trans2_r4_4_eq : ∀ k : Fin 16, trans2Expr 4 4 k = trans2_r4_4 k := by decide +kernel
lemma trans2_r4_5_eq : ∀ k : Fin 16, trans2Expr 4 5 k = trans2_r4_5 k := by decide +kernel
lemma trans2_r4_6_eq : ∀ k : Fin 16, trans2Expr 4 6 k = trans2_r4_6 k := by decide +kernel
lemma trans2_r4_7_eq : ∀ k : Fin 16, trans2Expr 4 7 k = trans2_r4_7 k := by decide +kernel
lemma trans2_r4_8_eq : ∀ k : Fin 16, trans2Expr 4 8 k = trans2_r4_8 k := by decide +kernel
lemma trans2_r4_9_eq : ∀ k : Fin 16, trans2Expr 4 9 k = trans2_r4_9 k := by decide +kernel
lemma trans2_r4_10_eq : ∀ k : Fin 16, trans2Expr 4 10 k = trans2_r4_10 k := by decide +kernel
lemma trans2_r4_11_eq : ∀ k : Fin 16, trans2Expr 4 11 k = trans2_r4_11 k := by decide +kernel
lemma trans2_r4_12_eq : ∀ k : Fin 16, trans2Expr 4 12 k = trans2_r4_12 k := by decide +kernel
lemma trans2_r4_13_eq : ∀ k : Fin 16, trans2Expr 4 13 k = trans2_r4_13 k := by decide +kernel
lemma trans2_r4_14_eq : ∀ k : Fin 16, trans2Expr 4 14 k = trans2_r4_14 k := by decide +kernel
lemma trans2_r4_15_eq : ∀ k : Fin 16, trans2Expr 4 15 k = trans2_r4_15 k := by decide +kernel
lemma trans2_r4_eq (i k : Fin 16) : trans2Expr 4 i k = trans2_r4 i k := by
  fin_cases i
  · exact trans2_r4_0_eq k
  · exact trans2_r4_1_eq k
  · exact trans2_r4_2_eq k
  · exact trans2_r4_3_eq k
  · exact trans2_r4_4_eq k
  · exact trans2_r4_5_eq k
  · exact trans2_r4_6_eq k
  · exact trans2_r4_7_eq k
  · exact trans2_r4_8_eq k
  · exact trans2_r4_9_eq k
  · exact trans2_r4_10_eq k
  · exact trans2_r4_11_eq k
  · exact trans2_r4_12_eq k
  · exact trans2_r4_13_eq k
  · exact trans2_r4_14_eq k
  · exact trans2_r4_15_eq k
lemma trans2_r5_0_eq : ∀ k : Fin 16, trans2Expr 5 0 k = trans2_r5_0 k := by decide +kernel
lemma trans2_r5_1_eq : ∀ k : Fin 16, trans2Expr 5 1 k = trans2_r5_1 k := by decide +kernel
lemma trans2_r5_2_eq : ∀ k : Fin 16, trans2Expr 5 2 k = trans2_r5_2 k := by decide +kernel
lemma trans2_r5_3_eq : ∀ k : Fin 16, trans2Expr 5 3 k = trans2_r5_3 k := by decide +kernel
lemma trans2_r5_4_eq : ∀ k : Fin 16, trans2Expr 5 4 k = trans2_r5_4 k := by decide +kernel
lemma trans2_r5_5_eq : ∀ k : Fin 16, trans2Expr 5 5 k = trans2_r5_5 k := by decide +kernel
lemma trans2_r5_6_eq : ∀ k : Fin 16, trans2Expr 5 6 k = trans2_r5_6 k := by decide +kernel
lemma trans2_r5_7_eq : ∀ k : Fin 16, trans2Expr 5 7 k = trans2_r5_7 k := by decide +kernel
lemma trans2_r5_8_eq : ∀ k : Fin 16, trans2Expr 5 8 k = trans2_r5_8 k := by decide +kernel
lemma trans2_r5_9_eq : ∀ k : Fin 16, trans2Expr 5 9 k = trans2_r5_9 k := by decide +kernel
lemma trans2_r5_10_eq : ∀ k : Fin 16, trans2Expr 5 10 k = trans2_r5_10 k := by decide +kernel
lemma trans2_r5_11_eq : ∀ k : Fin 16, trans2Expr 5 11 k = trans2_r5_11 k := by decide +kernel
lemma trans2_r5_12_eq : ∀ k : Fin 16, trans2Expr 5 12 k = trans2_r5_12 k := by decide +kernel
lemma trans2_r5_13_eq : ∀ k : Fin 16, trans2Expr 5 13 k = trans2_r5_13 k := by decide +kernel
lemma trans2_r5_14_eq : ∀ k : Fin 16, trans2Expr 5 14 k = trans2_r5_14 k := by decide +kernel
lemma trans2_r5_15_eq : ∀ k : Fin 16, trans2Expr 5 15 k = trans2_r5_15 k := by decide +kernel
lemma trans2_r5_eq (i k : Fin 16) : trans2Expr 5 i k = trans2_r5 i k := by
  fin_cases i
  · exact trans2_r5_0_eq k
  · exact trans2_r5_1_eq k
  · exact trans2_r5_2_eq k
  · exact trans2_r5_3_eq k
  · exact trans2_r5_4_eq k
  · exact trans2_r5_5_eq k
  · exact trans2_r5_6_eq k
  · exact trans2_r5_7_eq k
  · exact trans2_r5_8_eq k
  · exact trans2_r5_9_eq k
  · exact trans2_r5_10_eq k
  · exact trans2_r5_11_eq k
  · exact trans2_r5_12_eq k
  · exact trans2_r5_13_eq k
  · exact trans2_r5_14_eq k
  · exact trans2_r5_15_eq k
lemma trans2_eq (j : Fin 6) (i k : Fin 16) : trans2Expr j i k = trans2 j i k := by
  fin_cases j
  · exact trans2_r0_eq i k
  · exact trans2_r1_eq i k
  · exact trans2_r2_eq i k
  · exact trans2_r3_eq i k
  · exact trans2_r4_eq i k
  · exact trans2_r5_eq i k
lemma trans2_contains (j : Fin 6) (i k : Fin 16) :
    (trans2 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(2:ℕ))) := by
  rw [← trans2_eq]
  unfold trans2Expr
  convert exp_transformed_step (trans1_contains j i k) (transStep_contains j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
lemma trans3_r0_0_eq : ∀ k : Fin 16, trans3Expr 0 0 k = trans3_r0_0 k := by decide +kernel
lemma trans3_r0_1_eq : ∀ k : Fin 16, trans3Expr 0 1 k = trans3_r0_1 k := by decide +kernel
lemma trans3_r0_2_eq : ∀ k : Fin 16, trans3Expr 0 2 k = trans3_r0_2 k := by decide +kernel
lemma trans3_r0_3_eq : ∀ k : Fin 16, trans3Expr 0 3 k = trans3_r0_3 k := by decide +kernel
lemma trans3_r0_4_eq : ∀ k : Fin 16, trans3Expr 0 4 k = trans3_r0_4 k := by decide +kernel
lemma trans3_r0_5_eq : ∀ k : Fin 16, trans3Expr 0 5 k = trans3_r0_5 k := by decide +kernel
lemma trans3_r0_6_eq : ∀ k : Fin 16, trans3Expr 0 6 k = trans3_r0_6 k := by decide +kernel
lemma trans3_r0_7_eq : ∀ k : Fin 16, trans3Expr 0 7 k = trans3_r0_7 k := by decide +kernel
lemma trans3_r0_8_eq : ∀ k : Fin 16, trans3Expr 0 8 k = trans3_r0_8 k := by decide +kernel
lemma trans3_r0_9_eq : ∀ k : Fin 16, trans3Expr 0 9 k = trans3_r0_9 k := by decide +kernel
lemma trans3_r0_10_eq : ∀ k : Fin 16, trans3Expr 0 10 k = trans3_r0_10 k := by decide +kernel
lemma trans3_r0_11_eq : ∀ k : Fin 16, trans3Expr 0 11 k = trans3_r0_11 k := by decide +kernel
lemma trans3_r0_12_eq : ∀ k : Fin 16, trans3Expr 0 12 k = trans3_r0_12 k := by decide +kernel
lemma trans3_r0_13_eq : ∀ k : Fin 16, trans3Expr 0 13 k = trans3_r0_13 k := by decide +kernel
lemma trans3_r0_14_eq : ∀ k : Fin 16, trans3Expr 0 14 k = trans3_r0_14 k := by decide +kernel
lemma trans3_r0_15_eq : ∀ k : Fin 16, trans3Expr 0 15 k = trans3_r0_15 k := by decide +kernel
lemma trans3_r0_eq (i k : Fin 16) : trans3Expr 0 i k = trans3_r0 i k := by
  fin_cases i
  · exact trans3_r0_0_eq k
  · exact trans3_r0_1_eq k
  · exact trans3_r0_2_eq k
  · exact trans3_r0_3_eq k
  · exact trans3_r0_4_eq k
  · exact trans3_r0_5_eq k
  · exact trans3_r0_6_eq k
  · exact trans3_r0_7_eq k
  · exact trans3_r0_8_eq k
  · exact trans3_r0_9_eq k
  · exact trans3_r0_10_eq k
  · exact trans3_r0_11_eq k
  · exact trans3_r0_12_eq k
  · exact trans3_r0_13_eq k
  · exact trans3_r0_14_eq k
  · exact trans3_r0_15_eq k
lemma trans3_r1_0_eq : ∀ k : Fin 16, trans3Expr 1 0 k = trans3_r1_0 k := by decide +kernel
lemma trans3_r1_1_eq : ∀ k : Fin 16, trans3Expr 1 1 k = trans3_r1_1 k := by decide +kernel
lemma trans3_r1_2_eq : ∀ k : Fin 16, trans3Expr 1 2 k = trans3_r1_2 k := by decide +kernel
lemma trans3_r1_3_eq : ∀ k : Fin 16, trans3Expr 1 3 k = trans3_r1_3 k := by decide +kernel
lemma trans3_r1_4_eq : ∀ k : Fin 16, trans3Expr 1 4 k = trans3_r1_4 k := by decide +kernel
lemma trans3_r1_5_eq : ∀ k : Fin 16, trans3Expr 1 5 k = trans3_r1_5 k := by decide +kernel
lemma trans3_r1_6_eq : ∀ k : Fin 16, trans3Expr 1 6 k = trans3_r1_6 k := by decide +kernel
lemma trans3_r1_7_eq : ∀ k : Fin 16, trans3Expr 1 7 k = trans3_r1_7 k := by decide +kernel
lemma trans3_r1_8_eq : ∀ k : Fin 16, trans3Expr 1 8 k = trans3_r1_8 k := by decide +kernel
lemma trans3_r1_9_eq : ∀ k : Fin 16, trans3Expr 1 9 k = trans3_r1_9 k := by decide +kernel
lemma trans3_r1_10_eq : ∀ k : Fin 16, trans3Expr 1 10 k = trans3_r1_10 k := by decide +kernel
lemma trans3_r1_11_eq : ∀ k : Fin 16, trans3Expr 1 11 k = trans3_r1_11 k := by decide +kernel
lemma trans3_r1_12_eq : ∀ k : Fin 16, trans3Expr 1 12 k = trans3_r1_12 k := by decide +kernel
lemma trans3_r1_13_eq : ∀ k : Fin 16, trans3Expr 1 13 k = trans3_r1_13 k := by decide +kernel
lemma trans3_r1_14_eq : ∀ k : Fin 16, trans3Expr 1 14 k = trans3_r1_14 k := by decide +kernel
lemma trans3_r1_15_eq : ∀ k : Fin 16, trans3Expr 1 15 k = trans3_r1_15 k := by decide +kernel
lemma trans3_r1_eq (i k : Fin 16) : trans3Expr 1 i k = trans3_r1 i k := by
  fin_cases i
  · exact trans3_r1_0_eq k
  · exact trans3_r1_1_eq k
  · exact trans3_r1_2_eq k
  · exact trans3_r1_3_eq k
  · exact trans3_r1_4_eq k
  · exact trans3_r1_5_eq k
  · exact trans3_r1_6_eq k
  · exact trans3_r1_7_eq k
  · exact trans3_r1_8_eq k
  · exact trans3_r1_9_eq k
  · exact trans3_r1_10_eq k
  · exact trans3_r1_11_eq k
  · exact trans3_r1_12_eq k
  · exact trans3_r1_13_eq k
  · exact trans3_r1_14_eq k
  · exact trans3_r1_15_eq k
lemma trans3_r2_0_eq : ∀ k : Fin 16, trans3Expr 2 0 k = trans3_r2_0 k := by decide +kernel
lemma trans3_r2_1_eq : ∀ k : Fin 16, trans3Expr 2 1 k = trans3_r2_1 k := by decide +kernel
lemma trans3_r2_2_eq : ∀ k : Fin 16, trans3Expr 2 2 k = trans3_r2_2 k := by decide +kernel
lemma trans3_r2_3_eq : ∀ k : Fin 16, trans3Expr 2 3 k = trans3_r2_3 k := by decide +kernel
lemma trans3_r2_4_eq : ∀ k : Fin 16, trans3Expr 2 4 k = trans3_r2_4 k := by decide +kernel
lemma trans3_r2_5_eq : ∀ k : Fin 16, trans3Expr 2 5 k = trans3_r2_5 k := by decide +kernel
lemma trans3_r2_6_eq : ∀ k : Fin 16, trans3Expr 2 6 k = trans3_r2_6 k := by decide +kernel
lemma trans3_r2_7_eq : ∀ k : Fin 16, trans3Expr 2 7 k = trans3_r2_7 k := by decide +kernel
lemma trans3_r2_8_eq : ∀ k : Fin 16, trans3Expr 2 8 k = trans3_r2_8 k := by decide +kernel
lemma trans3_r2_9_eq : ∀ k : Fin 16, trans3Expr 2 9 k = trans3_r2_9 k := by decide +kernel
lemma trans3_r2_10_eq : ∀ k : Fin 16, trans3Expr 2 10 k = trans3_r2_10 k := by decide +kernel
lemma trans3_r2_11_eq : ∀ k : Fin 16, trans3Expr 2 11 k = trans3_r2_11 k := by decide +kernel
lemma trans3_r2_12_eq : ∀ k : Fin 16, trans3Expr 2 12 k = trans3_r2_12 k := by decide +kernel
lemma trans3_r2_13_eq : ∀ k : Fin 16, trans3Expr 2 13 k = trans3_r2_13 k := by decide +kernel
lemma trans3_r2_14_eq : ∀ k : Fin 16, trans3Expr 2 14 k = trans3_r2_14 k := by decide +kernel
lemma trans3_r2_15_eq : ∀ k : Fin 16, trans3Expr 2 15 k = trans3_r2_15 k := by decide +kernel
lemma trans3_r2_eq (i k : Fin 16) : trans3Expr 2 i k = trans3_r2 i k := by
  fin_cases i
  · exact trans3_r2_0_eq k
  · exact trans3_r2_1_eq k
  · exact trans3_r2_2_eq k
  · exact trans3_r2_3_eq k
  · exact trans3_r2_4_eq k
  · exact trans3_r2_5_eq k
  · exact trans3_r2_6_eq k
  · exact trans3_r2_7_eq k
  · exact trans3_r2_8_eq k
  · exact trans3_r2_9_eq k
  · exact trans3_r2_10_eq k
  · exact trans3_r2_11_eq k
  · exact trans3_r2_12_eq k
  · exact trans3_r2_13_eq k
  · exact trans3_r2_14_eq k
  · exact trans3_r2_15_eq k
lemma trans3_r3_0_eq : ∀ k : Fin 16, trans3Expr 3 0 k = trans3_r3_0 k := by decide +kernel
lemma trans3_r3_1_eq : ∀ k : Fin 16, trans3Expr 3 1 k = trans3_r3_1 k := by decide +kernel
lemma trans3_r3_2_eq : ∀ k : Fin 16, trans3Expr 3 2 k = trans3_r3_2 k := by decide +kernel
lemma trans3_r3_3_eq : ∀ k : Fin 16, trans3Expr 3 3 k = trans3_r3_3 k := by decide +kernel
lemma trans3_r3_4_eq : ∀ k : Fin 16, trans3Expr 3 4 k = trans3_r3_4 k := by decide +kernel
lemma trans3_r3_5_eq : ∀ k : Fin 16, trans3Expr 3 5 k = trans3_r3_5 k := by decide +kernel
lemma trans3_r3_6_eq : ∀ k : Fin 16, trans3Expr 3 6 k = trans3_r3_6 k := by decide +kernel
lemma trans3_r3_7_eq : ∀ k : Fin 16, trans3Expr 3 7 k = trans3_r3_7 k := by decide +kernel
lemma trans3_r3_8_eq : ∀ k : Fin 16, trans3Expr 3 8 k = trans3_r3_8 k := by decide +kernel
lemma trans3_r3_9_eq : ∀ k : Fin 16, trans3Expr 3 9 k = trans3_r3_9 k := by decide +kernel
lemma trans3_r3_10_eq : ∀ k : Fin 16, trans3Expr 3 10 k = trans3_r3_10 k := by decide +kernel
lemma trans3_r3_11_eq : ∀ k : Fin 16, trans3Expr 3 11 k = trans3_r3_11 k := by decide +kernel
lemma trans3_r3_12_eq : ∀ k : Fin 16, trans3Expr 3 12 k = trans3_r3_12 k := by decide +kernel
lemma trans3_r3_13_eq : ∀ k : Fin 16, trans3Expr 3 13 k = trans3_r3_13 k := by decide +kernel
lemma trans3_r3_14_eq : ∀ k : Fin 16, trans3Expr 3 14 k = trans3_r3_14 k := by decide +kernel
lemma trans3_r3_15_eq : ∀ k : Fin 16, trans3Expr 3 15 k = trans3_r3_15 k := by decide +kernel
lemma trans3_r3_eq (i k : Fin 16) : trans3Expr 3 i k = trans3_r3 i k := by
  fin_cases i
  · exact trans3_r3_0_eq k
  · exact trans3_r3_1_eq k
  · exact trans3_r3_2_eq k
  · exact trans3_r3_3_eq k
  · exact trans3_r3_4_eq k
  · exact trans3_r3_5_eq k
  · exact trans3_r3_6_eq k
  · exact trans3_r3_7_eq k
  · exact trans3_r3_8_eq k
  · exact trans3_r3_9_eq k
  · exact trans3_r3_10_eq k
  · exact trans3_r3_11_eq k
  · exact trans3_r3_12_eq k
  · exact trans3_r3_13_eq k
  · exact trans3_r3_14_eq k
  · exact trans3_r3_15_eq k
lemma trans3_r4_0_eq : ∀ k : Fin 16, trans3Expr 4 0 k = trans3_r4_0 k := by decide +kernel
lemma trans3_r4_1_eq : ∀ k : Fin 16, trans3Expr 4 1 k = trans3_r4_1 k := by decide +kernel
lemma trans3_r4_2_eq : ∀ k : Fin 16, trans3Expr 4 2 k = trans3_r4_2 k := by decide +kernel
lemma trans3_r4_3_eq : ∀ k : Fin 16, trans3Expr 4 3 k = trans3_r4_3 k := by decide +kernel
lemma trans3_r4_4_eq : ∀ k : Fin 16, trans3Expr 4 4 k = trans3_r4_4 k := by decide +kernel
lemma trans3_r4_5_eq : ∀ k : Fin 16, trans3Expr 4 5 k = trans3_r4_5 k := by decide +kernel
lemma trans3_r4_6_eq : ∀ k : Fin 16, trans3Expr 4 6 k = trans3_r4_6 k := by decide +kernel
lemma trans3_r4_7_eq : ∀ k : Fin 16, trans3Expr 4 7 k = trans3_r4_7 k := by decide +kernel
lemma trans3_r4_8_eq : ∀ k : Fin 16, trans3Expr 4 8 k = trans3_r4_8 k := by decide +kernel
lemma trans3_r4_9_eq : ∀ k : Fin 16, trans3Expr 4 9 k = trans3_r4_9 k := by decide +kernel
lemma trans3_r4_10_eq : ∀ k : Fin 16, trans3Expr 4 10 k = trans3_r4_10 k := by decide +kernel
lemma trans3_r4_11_eq : ∀ k : Fin 16, trans3Expr 4 11 k = trans3_r4_11 k := by decide +kernel
lemma trans3_r4_12_eq : ∀ k : Fin 16, trans3Expr 4 12 k = trans3_r4_12 k := by decide +kernel
lemma trans3_r4_13_eq : ∀ k : Fin 16, trans3Expr 4 13 k = trans3_r4_13 k := by decide +kernel
lemma trans3_r4_14_eq : ∀ k : Fin 16, trans3Expr 4 14 k = trans3_r4_14 k := by decide +kernel
lemma trans3_r4_15_eq : ∀ k : Fin 16, trans3Expr 4 15 k = trans3_r4_15 k := by decide +kernel
lemma trans3_r4_eq (i k : Fin 16) : trans3Expr 4 i k = trans3_r4 i k := by
  fin_cases i
  · exact trans3_r4_0_eq k
  · exact trans3_r4_1_eq k
  · exact trans3_r4_2_eq k
  · exact trans3_r4_3_eq k
  · exact trans3_r4_4_eq k
  · exact trans3_r4_5_eq k
  · exact trans3_r4_6_eq k
  · exact trans3_r4_7_eq k
  · exact trans3_r4_8_eq k
  · exact trans3_r4_9_eq k
  · exact trans3_r4_10_eq k
  · exact trans3_r4_11_eq k
  · exact trans3_r4_12_eq k
  · exact trans3_r4_13_eq k
  · exact trans3_r4_14_eq k
  · exact trans3_r4_15_eq k
lemma trans3_r5_0_eq : ∀ k : Fin 16, trans3Expr 5 0 k = trans3_r5_0 k := by decide +kernel
lemma trans3_r5_1_eq : ∀ k : Fin 16, trans3Expr 5 1 k = trans3_r5_1 k := by decide +kernel
lemma trans3_r5_2_eq : ∀ k : Fin 16, trans3Expr 5 2 k = trans3_r5_2 k := by decide +kernel
lemma trans3_r5_3_eq : ∀ k : Fin 16, trans3Expr 5 3 k = trans3_r5_3 k := by decide +kernel
lemma trans3_r5_4_eq : ∀ k : Fin 16, trans3Expr 5 4 k = trans3_r5_4 k := by decide +kernel
lemma trans3_r5_5_eq : ∀ k : Fin 16, trans3Expr 5 5 k = trans3_r5_5 k := by decide +kernel
lemma trans3_r5_6_eq : ∀ k : Fin 16, trans3Expr 5 6 k = trans3_r5_6 k := by decide +kernel
lemma trans3_r5_7_eq : ∀ k : Fin 16, trans3Expr 5 7 k = trans3_r5_7 k := by decide +kernel
lemma trans3_r5_8_eq : ∀ k : Fin 16, trans3Expr 5 8 k = trans3_r5_8 k := by decide +kernel
lemma trans3_r5_9_eq : ∀ k : Fin 16, trans3Expr 5 9 k = trans3_r5_9 k := by decide +kernel
lemma trans3_r5_10_eq : ∀ k : Fin 16, trans3Expr 5 10 k = trans3_r5_10 k := by decide +kernel
lemma trans3_r5_11_eq : ∀ k : Fin 16, trans3Expr 5 11 k = trans3_r5_11 k := by decide +kernel
lemma trans3_r5_12_eq : ∀ k : Fin 16, trans3Expr 5 12 k = trans3_r5_12 k := by decide +kernel
lemma trans3_r5_13_eq : ∀ k : Fin 16, trans3Expr 5 13 k = trans3_r5_13 k := by decide +kernel
lemma trans3_r5_14_eq : ∀ k : Fin 16, trans3Expr 5 14 k = trans3_r5_14 k := by decide +kernel
lemma trans3_r5_15_eq : ∀ k : Fin 16, trans3Expr 5 15 k = trans3_r5_15 k := by decide +kernel
lemma trans3_r5_eq (i k : Fin 16) : trans3Expr 5 i k = trans3_r5 i k := by
  fin_cases i
  · exact trans3_r5_0_eq k
  · exact trans3_r5_1_eq k
  · exact trans3_r5_2_eq k
  · exact trans3_r5_3_eq k
  · exact trans3_r5_4_eq k
  · exact trans3_r5_5_eq k
  · exact trans3_r5_6_eq k
  · exact trans3_r5_7_eq k
  · exact trans3_r5_8_eq k
  · exact trans3_r5_9_eq k
  · exact trans3_r5_10_eq k
  · exact trans3_r5_11_eq k
  · exact trans3_r5_12_eq k
  · exact trans3_r5_13_eq k
  · exact trans3_r5_14_eq k
  · exact trans3_r5_15_eq k
lemma trans3_eq (j : Fin 6) (i k : Fin 16) : trans3Expr j i k = trans3 j i k := by
  fin_cases j
  · exact trans3_r0_eq i k
  · exact trans3_r1_eq i k
  · exact trans3_r2_eq i k
  · exact trans3_r3_eq i k
  · exact trans3_r4_eq i k
  · exact trans3_r5_eq i k
lemma trans3_contains (j : Fin 6) (i k : Fin 16) :
    (trans3 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(3:ℕ))) := by
  rw [← trans3_eq]
  unfold trans3Expr
  convert exp_transformed_step (trans2_contains j i k) (transStep_contains j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
lemma kernel3_0_r0_0_eq : ∀ k : Fin 16, kernel3_0Expr 0 0 k = kernel3_0_r0_0 k := by decide +kernel
lemma kernel3_0_r0_1_eq : ∀ k : Fin 16, kernel3_0Expr 0 1 k = kernel3_0_r0_1 k := by decide +kernel
lemma kernel3_0_r0_2_eq : ∀ k : Fin 16, kernel3_0Expr 0 2 k = kernel3_0_r0_2 k := by decide +kernel
lemma kernel3_0_r0_3_eq : ∀ k : Fin 16, kernel3_0Expr 0 3 k = kernel3_0_r0_3 k := by decide +kernel
lemma kernel3_0_r0_4_eq : ∀ k : Fin 16, kernel3_0Expr 0 4 k = kernel3_0_r0_4 k := by decide +kernel
lemma kernel3_0_r0_5_eq : ∀ k : Fin 16, kernel3_0Expr 0 5 k = kernel3_0_r0_5 k := by decide +kernel
lemma kernel3_0_r0_6_eq : ∀ k : Fin 16, kernel3_0Expr 0 6 k = kernel3_0_r0_6 k := by decide +kernel
lemma kernel3_0_r0_7_eq : ∀ k : Fin 16, kernel3_0Expr 0 7 k = kernel3_0_r0_7 k := by decide +kernel
lemma kernel3_0_r0_8_eq : ∀ k : Fin 16, kernel3_0Expr 0 8 k = kernel3_0_r0_8 k := by decide +kernel
lemma kernel3_0_r0_9_eq : ∀ k : Fin 16, kernel3_0Expr 0 9 k = kernel3_0_r0_9 k := by decide +kernel
lemma kernel3_0_r0_10_eq : ∀ k : Fin 16, kernel3_0Expr 0 10 k = kernel3_0_r0_10 k := by decide +kernel
lemma kernel3_0_r0_11_eq : ∀ k : Fin 16, kernel3_0Expr 0 11 k = kernel3_0_r0_11 k := by decide +kernel
lemma kernel3_0_r0_12_eq : ∀ k : Fin 16, kernel3_0Expr 0 12 k = kernel3_0_r0_12 k := by decide +kernel
lemma kernel3_0_r0_13_eq : ∀ k : Fin 16, kernel3_0Expr 0 13 k = kernel3_0_r0_13 k := by decide +kernel
lemma kernel3_0_r0_14_eq : ∀ k : Fin 16, kernel3_0Expr 0 14 k = kernel3_0_r0_14 k := by decide +kernel
lemma kernel3_0_r0_15_eq : ∀ k : Fin 16, kernel3_0Expr 0 15 k = kernel3_0_r0_15 k := by decide +kernel
lemma kernel3_0_r0_eq (i k : Fin 16) : kernel3_0Expr 0 i k = kernel3_0_r0 i k := by
  fin_cases i
  · exact kernel3_0_r0_0_eq k
  · exact kernel3_0_r0_1_eq k
  · exact kernel3_0_r0_2_eq k
  · exact kernel3_0_r0_3_eq k
  · exact kernel3_0_r0_4_eq k
  · exact kernel3_0_r0_5_eq k
  · exact kernel3_0_r0_6_eq k
  · exact kernel3_0_r0_7_eq k
  · exact kernel3_0_r0_8_eq k
  · exact kernel3_0_r0_9_eq k
  · exact kernel3_0_r0_10_eq k
  · exact kernel3_0_r0_11_eq k
  · exact kernel3_0_r0_12_eq k
  · exact kernel3_0_r0_13_eq k
  · exact kernel3_0_r0_14_eq k
  · exact kernel3_0_r0_15_eq k
lemma kernel3_0_r1_0_eq : ∀ k : Fin 16, kernel3_0Expr 1 0 k = kernel3_0_r1_0 k := by decide +kernel
lemma kernel3_0_r1_1_eq : ∀ k : Fin 16, kernel3_0Expr 1 1 k = kernel3_0_r1_1 k := by decide +kernel
lemma kernel3_0_r1_2_eq : ∀ k : Fin 16, kernel3_0Expr 1 2 k = kernel3_0_r1_2 k := by decide +kernel
lemma kernel3_0_r1_3_eq : ∀ k : Fin 16, kernel3_0Expr 1 3 k = kernel3_0_r1_3 k := by decide +kernel
lemma kernel3_0_r1_4_eq : ∀ k : Fin 16, kernel3_0Expr 1 4 k = kernel3_0_r1_4 k := by decide +kernel
lemma kernel3_0_r1_5_eq : ∀ k : Fin 16, kernel3_0Expr 1 5 k = kernel3_0_r1_5 k := by decide +kernel
lemma kernel3_0_r1_6_eq : ∀ k : Fin 16, kernel3_0Expr 1 6 k = kernel3_0_r1_6 k := by decide +kernel
lemma kernel3_0_r1_7_eq : ∀ k : Fin 16, kernel3_0Expr 1 7 k = kernel3_0_r1_7 k := by decide +kernel
lemma kernel3_0_r1_8_eq : ∀ k : Fin 16, kernel3_0Expr 1 8 k = kernel3_0_r1_8 k := by decide +kernel
lemma kernel3_0_r1_9_eq : ∀ k : Fin 16, kernel3_0Expr 1 9 k = kernel3_0_r1_9 k := by decide +kernel
lemma kernel3_0_r1_10_eq : ∀ k : Fin 16, kernel3_0Expr 1 10 k = kernel3_0_r1_10 k := by decide +kernel
lemma kernel3_0_r1_11_eq : ∀ k : Fin 16, kernel3_0Expr 1 11 k = kernel3_0_r1_11 k := by decide +kernel
lemma kernel3_0_r1_12_eq : ∀ k : Fin 16, kernel3_0Expr 1 12 k = kernel3_0_r1_12 k := by decide +kernel
lemma kernel3_0_r1_13_eq : ∀ k : Fin 16, kernel3_0Expr 1 13 k = kernel3_0_r1_13 k := by decide +kernel
lemma kernel3_0_r1_14_eq : ∀ k : Fin 16, kernel3_0Expr 1 14 k = kernel3_0_r1_14 k := by decide +kernel
lemma kernel3_0_r1_15_eq : ∀ k : Fin 16, kernel3_0Expr 1 15 k = kernel3_0_r1_15 k := by decide +kernel
lemma kernel3_0_r1_eq (i k : Fin 16) : kernel3_0Expr 1 i k = kernel3_0_r1 i k := by
  fin_cases i
  · exact kernel3_0_r1_0_eq k
  · exact kernel3_0_r1_1_eq k
  · exact kernel3_0_r1_2_eq k
  · exact kernel3_0_r1_3_eq k
  · exact kernel3_0_r1_4_eq k
  · exact kernel3_0_r1_5_eq k
  · exact kernel3_0_r1_6_eq k
  · exact kernel3_0_r1_7_eq k
  · exact kernel3_0_r1_8_eq k
  · exact kernel3_0_r1_9_eq k
  · exact kernel3_0_r1_10_eq k
  · exact kernel3_0_r1_11_eq k
  · exact kernel3_0_r1_12_eq k
  · exact kernel3_0_r1_13_eq k
  · exact kernel3_0_r1_14_eq k
  · exact kernel3_0_r1_15_eq k
lemma kernel3_0_r2_0_eq : ∀ k : Fin 16, kernel3_0Expr 2 0 k = kernel3_0_r2_0 k := by decide +kernel
lemma kernel3_0_r2_1_eq : ∀ k : Fin 16, kernel3_0Expr 2 1 k = kernel3_0_r2_1 k := by decide +kernel
lemma kernel3_0_r2_2_eq : ∀ k : Fin 16, kernel3_0Expr 2 2 k = kernel3_0_r2_2 k := by decide +kernel
lemma kernel3_0_r2_3_eq : ∀ k : Fin 16, kernel3_0Expr 2 3 k = kernel3_0_r2_3 k := by decide +kernel
lemma kernel3_0_r2_4_eq : ∀ k : Fin 16, kernel3_0Expr 2 4 k = kernel3_0_r2_4 k := by decide +kernel
lemma kernel3_0_r2_5_eq : ∀ k : Fin 16, kernel3_0Expr 2 5 k = kernel3_0_r2_5 k := by decide +kernel
lemma kernel3_0_r2_6_eq : ∀ k : Fin 16, kernel3_0Expr 2 6 k = kernel3_0_r2_6 k := by decide +kernel
lemma kernel3_0_r2_7_eq : ∀ k : Fin 16, kernel3_0Expr 2 7 k = kernel3_0_r2_7 k := by decide +kernel
lemma kernel3_0_r2_8_eq : ∀ k : Fin 16, kernel3_0Expr 2 8 k = kernel3_0_r2_8 k := by decide +kernel
lemma kernel3_0_r2_9_eq : ∀ k : Fin 16, kernel3_0Expr 2 9 k = kernel3_0_r2_9 k := by decide +kernel
lemma kernel3_0_r2_10_eq : ∀ k : Fin 16, kernel3_0Expr 2 10 k = kernel3_0_r2_10 k := by decide +kernel
lemma kernel3_0_r2_11_eq : ∀ k : Fin 16, kernel3_0Expr 2 11 k = kernel3_0_r2_11 k := by decide +kernel
lemma kernel3_0_r2_12_eq : ∀ k : Fin 16, kernel3_0Expr 2 12 k = kernel3_0_r2_12 k := by decide +kernel
lemma kernel3_0_r2_13_eq : ∀ k : Fin 16, kernel3_0Expr 2 13 k = kernel3_0_r2_13 k := by decide +kernel
lemma kernel3_0_r2_14_eq : ∀ k : Fin 16, kernel3_0Expr 2 14 k = kernel3_0_r2_14 k := by decide +kernel
lemma kernel3_0_r2_15_eq : ∀ k : Fin 16, kernel3_0Expr 2 15 k = kernel3_0_r2_15 k := by decide +kernel
lemma kernel3_0_r2_eq (i k : Fin 16) : kernel3_0Expr 2 i k = kernel3_0_r2 i k := by
  fin_cases i
  · exact kernel3_0_r2_0_eq k
  · exact kernel3_0_r2_1_eq k
  · exact kernel3_0_r2_2_eq k
  · exact kernel3_0_r2_3_eq k
  · exact kernel3_0_r2_4_eq k
  · exact kernel3_0_r2_5_eq k
  · exact kernel3_0_r2_6_eq k
  · exact kernel3_0_r2_7_eq k
  · exact kernel3_0_r2_8_eq k
  · exact kernel3_0_r2_9_eq k
  · exact kernel3_0_r2_10_eq k
  · exact kernel3_0_r2_11_eq k
  · exact kernel3_0_r2_12_eq k
  · exact kernel3_0_r2_13_eq k
  · exact kernel3_0_r2_14_eq k
  · exact kernel3_0_r2_15_eq k
lemma kernel3_0_r3_0_eq : ∀ k : Fin 16, kernel3_0Expr 3 0 k = kernel3_0_r3_0 k := by decide +kernel
lemma kernel3_0_r3_1_eq : ∀ k : Fin 16, kernel3_0Expr 3 1 k = kernel3_0_r3_1 k := by decide +kernel
lemma kernel3_0_r3_2_eq : ∀ k : Fin 16, kernel3_0Expr 3 2 k = kernel3_0_r3_2 k := by decide +kernel
lemma kernel3_0_r3_3_eq : ∀ k : Fin 16, kernel3_0Expr 3 3 k = kernel3_0_r3_3 k := by decide +kernel
lemma kernel3_0_r3_4_eq : ∀ k : Fin 16, kernel3_0Expr 3 4 k = kernel3_0_r3_4 k := by decide +kernel
lemma kernel3_0_r3_5_eq : ∀ k : Fin 16, kernel3_0Expr 3 5 k = kernel3_0_r3_5 k := by decide +kernel
lemma kernel3_0_r3_6_eq : ∀ k : Fin 16, kernel3_0Expr 3 6 k = kernel3_0_r3_6 k := by decide +kernel
lemma kernel3_0_r3_7_eq : ∀ k : Fin 16, kernel3_0Expr 3 7 k = kernel3_0_r3_7 k := by decide +kernel
lemma kernel3_0_r3_8_eq : ∀ k : Fin 16, kernel3_0Expr 3 8 k = kernel3_0_r3_8 k := by decide +kernel
lemma kernel3_0_r3_9_eq : ∀ k : Fin 16, kernel3_0Expr 3 9 k = kernel3_0_r3_9 k := by decide +kernel
lemma kernel3_0_r3_10_eq : ∀ k : Fin 16, kernel3_0Expr 3 10 k = kernel3_0_r3_10 k := by decide +kernel
lemma kernel3_0_r3_11_eq : ∀ k : Fin 16, kernel3_0Expr 3 11 k = kernel3_0_r3_11 k := by decide +kernel
lemma kernel3_0_r3_12_eq : ∀ k : Fin 16, kernel3_0Expr 3 12 k = kernel3_0_r3_12 k := by decide +kernel
lemma kernel3_0_r3_13_eq : ∀ k : Fin 16, kernel3_0Expr 3 13 k = kernel3_0_r3_13 k := by decide +kernel
lemma kernel3_0_r3_14_eq : ∀ k : Fin 16, kernel3_0Expr 3 14 k = kernel3_0_r3_14 k := by decide +kernel
lemma kernel3_0_r3_15_eq : ∀ k : Fin 16, kernel3_0Expr 3 15 k = kernel3_0_r3_15 k := by decide +kernel
lemma kernel3_0_r3_eq (i k : Fin 16) : kernel3_0Expr 3 i k = kernel3_0_r3 i k := by
  fin_cases i
  · exact kernel3_0_r3_0_eq k
  · exact kernel3_0_r3_1_eq k
  · exact kernel3_0_r3_2_eq k
  · exact kernel3_0_r3_3_eq k
  · exact kernel3_0_r3_4_eq k
  · exact kernel3_0_r3_5_eq k
  · exact kernel3_0_r3_6_eq k
  · exact kernel3_0_r3_7_eq k
  · exact kernel3_0_r3_8_eq k
  · exact kernel3_0_r3_9_eq k
  · exact kernel3_0_r3_10_eq k
  · exact kernel3_0_r3_11_eq k
  · exact kernel3_0_r3_12_eq k
  · exact kernel3_0_r3_13_eq k
  · exact kernel3_0_r3_14_eq k
  · exact kernel3_0_r3_15_eq k
lemma kernel3_0_r4_0_eq : ∀ k : Fin 16, kernel3_0Expr 4 0 k = kernel3_0_r4_0 k := by decide +kernel
lemma kernel3_0_r4_1_eq : ∀ k : Fin 16, kernel3_0Expr 4 1 k = kernel3_0_r4_1 k := by decide +kernel
lemma kernel3_0_r4_2_eq : ∀ k : Fin 16, kernel3_0Expr 4 2 k = kernel3_0_r4_2 k := by decide +kernel
lemma kernel3_0_r4_3_eq : ∀ k : Fin 16, kernel3_0Expr 4 3 k = kernel3_0_r4_3 k := by decide +kernel
lemma kernel3_0_r4_4_eq : ∀ k : Fin 16, kernel3_0Expr 4 4 k = kernel3_0_r4_4 k := by decide +kernel
lemma kernel3_0_r4_5_eq : ∀ k : Fin 16, kernel3_0Expr 4 5 k = kernel3_0_r4_5 k := by decide +kernel
lemma kernel3_0_r4_6_eq : ∀ k : Fin 16, kernel3_0Expr 4 6 k = kernel3_0_r4_6 k := by decide +kernel
lemma kernel3_0_r4_7_eq : ∀ k : Fin 16, kernel3_0Expr 4 7 k = kernel3_0_r4_7 k := by decide +kernel
lemma kernel3_0_r4_8_eq : ∀ k : Fin 16, kernel3_0Expr 4 8 k = kernel3_0_r4_8 k := by decide +kernel
lemma kernel3_0_r4_9_eq : ∀ k : Fin 16, kernel3_0Expr 4 9 k = kernel3_0_r4_9 k := by decide +kernel
lemma kernel3_0_r4_10_eq : ∀ k : Fin 16, kernel3_0Expr 4 10 k = kernel3_0_r4_10 k := by decide +kernel
lemma kernel3_0_r4_11_eq : ∀ k : Fin 16, kernel3_0Expr 4 11 k = kernel3_0_r4_11 k := by decide +kernel
lemma kernel3_0_r4_12_eq : ∀ k : Fin 16, kernel3_0Expr 4 12 k = kernel3_0_r4_12 k := by decide +kernel
lemma kernel3_0_r4_13_eq : ∀ k : Fin 16, kernel3_0Expr 4 13 k = kernel3_0_r4_13 k := by decide +kernel
lemma kernel3_0_r4_14_eq : ∀ k : Fin 16, kernel3_0Expr 4 14 k = kernel3_0_r4_14 k := by decide +kernel
lemma kernel3_0_r4_15_eq : ∀ k : Fin 16, kernel3_0Expr 4 15 k = kernel3_0_r4_15 k := by decide +kernel
lemma kernel3_0_r4_eq (i k : Fin 16) : kernel3_0Expr 4 i k = kernel3_0_r4 i k := by
  fin_cases i
  · exact kernel3_0_r4_0_eq k
  · exact kernel3_0_r4_1_eq k
  · exact kernel3_0_r4_2_eq k
  · exact kernel3_0_r4_3_eq k
  · exact kernel3_0_r4_4_eq k
  · exact kernel3_0_r4_5_eq k
  · exact kernel3_0_r4_6_eq k
  · exact kernel3_0_r4_7_eq k
  · exact kernel3_0_r4_8_eq k
  · exact kernel3_0_r4_9_eq k
  · exact kernel3_0_r4_10_eq k
  · exact kernel3_0_r4_11_eq k
  · exact kernel3_0_r4_12_eq k
  · exact kernel3_0_r4_13_eq k
  · exact kernel3_0_r4_14_eq k
  · exact kernel3_0_r4_15_eq k
lemma kernel3_0_r5_0_eq : ∀ k : Fin 16, kernel3_0Expr 5 0 k = kernel3_0_r5_0 k := by decide +kernel
lemma kernel3_0_r5_1_eq : ∀ k : Fin 16, kernel3_0Expr 5 1 k = kernel3_0_r5_1 k := by decide +kernel
lemma kernel3_0_r5_2_eq : ∀ k : Fin 16, kernel3_0Expr 5 2 k = kernel3_0_r5_2 k := by decide +kernel
lemma kernel3_0_r5_3_eq : ∀ k : Fin 16, kernel3_0Expr 5 3 k = kernel3_0_r5_3 k := by decide +kernel
lemma kernel3_0_r5_4_eq : ∀ k : Fin 16, kernel3_0Expr 5 4 k = kernel3_0_r5_4 k := by decide +kernel
lemma kernel3_0_r5_5_eq : ∀ k : Fin 16, kernel3_0Expr 5 5 k = kernel3_0_r5_5 k := by decide +kernel
lemma kernel3_0_r5_6_eq : ∀ k : Fin 16, kernel3_0Expr 5 6 k = kernel3_0_r5_6 k := by decide +kernel
lemma kernel3_0_r5_7_eq : ∀ k : Fin 16, kernel3_0Expr 5 7 k = kernel3_0_r5_7 k := by decide +kernel
lemma kernel3_0_r5_8_eq : ∀ k : Fin 16, kernel3_0Expr 5 8 k = kernel3_0_r5_8 k := by decide +kernel
lemma kernel3_0_r5_9_eq : ∀ k : Fin 16, kernel3_0Expr 5 9 k = kernel3_0_r5_9 k := by decide +kernel
lemma kernel3_0_r5_10_eq : ∀ k : Fin 16, kernel3_0Expr 5 10 k = kernel3_0_r5_10 k := by decide +kernel
lemma kernel3_0_r5_11_eq : ∀ k : Fin 16, kernel3_0Expr 5 11 k = kernel3_0_r5_11 k := by decide +kernel
lemma kernel3_0_r5_12_eq : ∀ k : Fin 16, kernel3_0Expr 5 12 k = kernel3_0_r5_12 k := by decide +kernel
lemma kernel3_0_r5_13_eq : ∀ k : Fin 16, kernel3_0Expr 5 13 k = kernel3_0_r5_13 k := by decide +kernel
lemma kernel3_0_r5_14_eq : ∀ k : Fin 16, kernel3_0Expr 5 14 k = kernel3_0_r5_14 k := by decide +kernel
lemma kernel3_0_r5_15_eq : ∀ k : Fin 16, kernel3_0Expr 5 15 k = kernel3_0_r5_15 k := by decide +kernel
lemma kernel3_0_r5_eq (i k : Fin 16) : kernel3_0Expr 5 i k = kernel3_0_r5 i k := by
  fin_cases i
  · exact kernel3_0_r5_0_eq k
  · exact kernel3_0_r5_1_eq k
  · exact kernel3_0_r5_2_eq k
  · exact kernel3_0_r5_3_eq k
  · exact kernel3_0_r5_4_eq k
  · exact kernel3_0_r5_5_eq k
  · exact kernel3_0_r5_6_eq k
  · exact kernel3_0_r5_7_eq k
  · exact kernel3_0_r5_8_eq k
  · exact kernel3_0_r5_9_eq k
  · exact kernel3_0_r5_10_eq k
  · exact kernel3_0_r5_11_eq k
  · exact kernel3_0_r5_12_eq k
  · exact kernel3_0_r5_13_eq k
  · exact kernel3_0_r5_14_eq k
  · exact kernel3_0_r5_15_eq k
lemma kernel3_0_eq (j : Fin 6) (i k : Fin 16) : kernel3_0Expr j i k = kernel3_0 j i k := by
  fin_cases j
  · exact kernel3_0_r0_eq i k
  · exact kernel3_0_r1_eq i k
  · exact kernel3_0_r2_eq i k
  · exact kernel3_0_r3_eq i k
  · exact kernel3_0_r4_eq i k
  · exact kernel3_0_r5_eq i k
lemma kernel3_0_contains_e_oai (j : Fin 6) (i k : Fin 16) :
    (kernel3_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(3:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel3_0_eq]
  unfold kernel3_0Expr
  have hl := (gridRows_contains_e j i k).2.1
  rw [pointLambda_eq] at hl
  have hh := CBox.contains_mul_e hl (trans3_contains j i k)
  simpa only [Bool.false_eq_true,ite_false, if_false,mul_one] using hh
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.kernel3_0_contains_e_oai := @OAI.SharpPlanar.CachedData.kernel3_0_contains_e_oai
