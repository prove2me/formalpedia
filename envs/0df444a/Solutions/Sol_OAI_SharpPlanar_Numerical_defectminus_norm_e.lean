-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.defectminus_norm_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:05:40.974209+00:00
-- url     : https://prove2.me/submissions/1a6b70af-9dd0-470e-b752-f4460b990fde

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_CachedData_cm3_4_0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_column3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_cachedMomentRuleBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_K_column_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry0_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry0_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry0_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry0_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry0_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry0_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry1_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry1_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry1_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry1_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry1_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry1_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry2_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry2_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry2_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry2_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry2_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry3_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry3_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry3_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry3_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry3_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry3_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry4_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry4_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry4_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry4_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry4_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry5_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry5_1_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry5_2_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry5_3_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry5_4_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_dentry5_5_contains_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_S_apply_e
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

end IntegerIntervals
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DMoments3
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
namespace cm3_4_0_0
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox column3_0 kernel4_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 3 4 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_e column3_0_contains_e kernel4_0_contains_e
end cm3_4_0_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


lemma S_column_value (n m : Node) (d : Bool) :
    S (columnVector n d) (m,false) = -K (positiveData (columnVector n d)) 0 m.val / Q m.val := by
  simp [S_apply_e,Scoords]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma S_column_value_contains {n m : Node} {d : Bool} {a : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val)) :
    (a.neg.mul (qiBox m.val)).Contains (S (columnVector n d) (m,false)) := by
  rw [S_column_value,div_eq_mul_inv]
  exact RBox.contains_mul_e (RBox.neg_contains_e ha) (qiBox_contains_e m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DEntries
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

namespace SharpPlanar.Numerical
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma dentry2_1_contains : dentry2_1.Contains (S (columnVector node3 false) (node4,false)) := by
  have h0 := K_column_contains_e (n:=node3) (m:=4) (by decide) (by decide) false false cm3_4_0_0.contains
  have h1 := K_column_contains_e (n:=node3) (m:=4) (by decide) (by decide) false true cm3_4_0_1.contains_e
  have hh := S_column_value_contains (m:=node4) h0
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  decide +kernel
lemma dEntries_contains (i j : Fin 6) : (dEntries i j).Contains (Dmat i j) := by
  fin_cases i <;> fin_cases j
  · exact dentry0_0_contains_e
  · exact dentry0_1_contains_e
  · exact dentry0_2_contains_e
  · exact dentry0_3_contains_e
  · exact dentry0_4_contains_e
  · exact dentry0_5_contains_e
  · exact dentry1_0_contains_e
  · exact dentry1_1_contains_e
  · exact dentry1_2_contains_e
  · exact dentry1_3_contains_e
  · exact dentry1_4_contains_e
  · exact dentry1_5_contains_e
  · exact dentry2_0_contains_e
  · exact dentry2_1_contains
  · exact dentry2_2_contains_e
  · exact dentry2_3_contains_e
  · exact dentry2_4_contains_e
  · exact dentry2_5_contains_e
  · exact dentry3_0_contains_e
  · exact dentry3_1_contains_e
  · exact dentry3_2_contains_e
  · exact dentry3_3_contains_e
  · exact dentry3_4_contains_e
  · exact dentry3_5_contains_e
  · exact dentry4_0_contains_e
  · exact dentry4_1_contains_e
  · exact dentry4_2_contains_e
  · exact dentry4_3_contains_e
  · exact dentry4_4_contains_e
  · exact dentry4_5_contains_e
  · exact dentry5_0_contains_e
  · exact dentry5_1_contains_e
  · exact dentry5_2_contains_e
  · exact dentry5_3_contains_e
  · exact dentry5_4_contains_e
  · exact dentry5_5_contains_e
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals
open scoped BigOperators

lemma sumBox_contains {ι : Type*} [Fintype ι] {a : ι → RBox} {x : ι → ℝ}
    (ha : ∀ i, (a i).Contains (x i)) : (sumBox a).Contains (∑ i, x i) := by
  constructor
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).1)
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).2)

lemma matrixMulBox_contains {n m k : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {b : Matrix (Fin m) (Fin k) RBox} {A : Matrix (Fin n) (Fin m) ℝ}
    {B : Matrix (Fin m) (Fin k) ℝ} (ha : ∀ i j, (a i j).Contains (A i j))
    (hb : ∀ i j, (b i j).Contains (B i j)) (i j) :
    (matrixMulBox a b i j).Contains ((A*B) i j) := by
  exact sumBox_contains (fun l => RBox.contains_mul_e (ha i l) (hb l j))

lemma column_bound_lt {n m : ℕ} {a : Matrix (Fin n) (Fin m) RBox}
    {A : Matrix (Fin n) (Fin m) ℝ} {u v : ℤ} (hv : 0 < v)
    (ha : ∀ i j, (a i j).Contains (A i j))
    (hc : ∀ j, (∑ i, (a i j).bound)*v < precision*u) :
    ∀ j, ∑ i, |A i j| < (u:ℝ)/v := by
  intro j
  have h₁ : (precision:ℝ)*(∑ i, |A i j|) ≤ (∑ i, ((a i j).bound:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => RBox.abs_bound_e (ha i j)
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have h₂ : (∑ i, ((a i j).bound:ℝ))*(v:ℝ) < (precision:ℝ)*u := by
    exact_mod_cast hc j
  apply (mul_lt_mul_iff_right₀ precision_pos).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h₁ hv'.le) h₂

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
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

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
lemma WminusBox_contains (i j : Fin 6) : (WminusBox i j).Contains (Wminus i j) := RBox.contains_rat_e _ _ (by norm_num)
lemma AminusBox_contains (i j : Fin 6) : (AminusBox i j).Contains (Aminus i j) := by
  have hi : (RBox.rat (if i=j then 1 else 0) 1).Contains ((1:Matrix (Fin 6) (Fin 6) ℝ) i j) := by
    by_cases h : i=j <;> simp [Matrix.one_apply,h] <;> convert RBox.contains_rat_e _ 1 (by norm_num) using 1 <;> norm_num
  simpa only [AminusBox,Aminus,Matrix.add_apply,add_zero] using RBox.contains_add_e hi ((dEntries_contains i j))
lemma defectminusBox_contains (i j : Fin 6) : (defectminusBox i j).Contains ((1-Wminus*Aminus) i j) := by
  have hi : (RBox.rat (if i=j then 1 else 0) 1).Contains ((1:Matrix (Fin 6) (Fin 6) ℝ) i j) := by
    by_cases h : i=j <;> simp [Matrix.one_apply,h] <;> convert RBox.contains_rat_e _ 1 (by norm_num) using 1 <;> norm_num
  simpa only [defectminusBox,Matrix.sub_apply,sub_eq_add_neg] using RBox.contains_add_e hi (RBox.neg_contains_e (matrixMulBox_contains WminusBox_contains AminusBox_contains i j))
lemma defectminus_column (j : Fin 6) : ∑ i, |((1-Wminus*Aminus) i j)| < (1:ℝ)/1000 := by
  have hh := column_bound_lt (u:=1) (v:=1000) (a:=defectminusBox) (by norm_num) defectminusBox_contains (by
    intro k
    fin_cases k <;> decide +kernel) j
  simpa only [Int.cast_one,Int.cast_ofNat] using hh
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl

omit [DecidableEq ι] in
lemma matrixL1_mul (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixL1 (A*B) = (matrixL1 A).comp (matrixL1 B) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLpLin 1 1 (A*B) x = Matrix.toLpLin 1 1 A (Matrix.toLpLin 1 1 B x)
  rw [Matrix.toLpLin_mul (q:=1)]
  rfl
omit [DecidableEq ι] in
lemma matrixL1_sub (A B : Matrix ι κ ℝ) :
    matrixL1 (A-B) = matrixL1 A-matrixL1 B := by
  ext x i
  simp [matrixL1_apply,sub_mul,Finset.sum_sub_distrib]
lemma matrixL1_one : matrixL1 (1:Matrix ι ι ℝ) = 1 := by
  ext x i
  simp [matrixL1_apply,Matrix.one_apply]

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm_e,l1Finite_norm_e,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma defectminus_norm_e_oai : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectminus_column
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.defectminus_norm_e_oai := @OAI.SharpPlanar.Numerical.defectminus_norm_e_oai
