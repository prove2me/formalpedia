-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.U37.entry3_0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:50:34.847527+00:00
-- url     : https://prove2.me/submissions/bd6ba641-824f-4fad-959d-eb3ff218c576

import Mathlib
import Definitions.Def_OAIQ098G061
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G100
import Definitions.Def_OAIQ098G148
import Definitions.Def_OAIQ098G362
import Theorems.Thm_OAI_SharpPlanar_CachedData_column37_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel1_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel1_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_trans1_contains_g
import Theorems.Thm_OAI_SharpPlanar_D_0_g
import Theorems.Thm_OAI_SharpPlanar_D_1_g
import Theorems.Thm_OAI_SharpPlanar_D_3_g
import Theorems.Thm_OAI_SharpPlanar_D_4_g
import Theorems.Thm_OAI_SharpPlanar_D_7_g
import Theorems.Thm_OAI_SharpPlanar_D_9_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_cachedMomentRuleBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_K_column_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_S_apply_g

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
lemma kernel1_0_contains (j : Fin 6) (i k : Fin 16) :
    (kernel1_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(1:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel1_0_eq_g]
  unfold kernel1_0Expr
  have hl := (gridRows_contains_g j i k).2.1
  rw [pointLambda_eq_g] at hl
  have hh := CBox.contains_mul_g hl (trans1_contains_g j i k)
  simpa only [Bool.false_eq_true,ite_false, if_false,mul_one] using hh
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments37
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
namespace cm37_1_0_0
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
lemma checked : cachedMomentRuleBox column37_0 kernel1_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 37 1 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_g column37_0_contains_g kernel1_0_contains
end cm37_1_0_0
namespace cm37_1_0_1
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
lemma checked : cachedMomentRuleBox column37_0 kernel1_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 37 1 false true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains_g column37_0_contains_g kernel1_1_contains_g
end cm37_1_0_1
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


lemma S_column_derivative (n m : Node) (d : Bool) :
    S (columnVector n d) (m,true) =
      (D m.val * K (positiveData (columnVector n d)) 0 m.val -
        K (positiveData (columnVector n d)) 1 m.val) / Q m.val := by
  simp [S_apply_g,Scoords]

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

lemma dSmall_contains : dSmall.Contains (Real.pi*(3+2*b)/18) := by
  have hb := RBox.contains_add_g (RBox.contains_rat_g 3 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g 2 1 (by norm_num))
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dOther_contains : dOther.Contains (Real.pi*(3-2*b)/18) := by
  have hb := RBox.contains_add_g (RBox.contains_rat_g 3 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g (-2) 1 (by norm_num))
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dBase_contains : dBase.Contains (7*Real.pi*b/9) := by
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g bBounds_contains_g) 7 9 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)

lemma dBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (dBox n).Contains (D n) := by
  have hh : D n = D (n%12) := by simp [D]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn
  · simpa [D_0_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dBase_contains
  · simpa [D_1_g,hn,dBox] using dSmall_contains
  · simpa [D_3_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dSmall_contains
  · simpa [D_4_g,hn,dBox] using dBase_contains
  · simpa [D_7_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dOther_contains
  · simpa [D_9_g,hn,dBox] using dOther_contains

lemma S_column_derivative_contains {n m : Node} {d : Bool} {a c : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val))
    (hc : c.Contains (K (positiveData (columnVector n d)) 1 m.val)) :
    (((dBox m.val).mul a).add c.neg |>.mul (qiBox m.val)).Contains (S (columnVector n d) (m,true)) := by
  rw [S_column_derivative,div_eq_mul_inv,sub_eq_add_neg]
  exact RBox.contains_mul_g
    (RBox.contains_add_g (RBox.contains_mul_g (dBox_contains m.val m.property.2) ha) (RBox.neg_contains_g hc))
    (qiBox_contains_g m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert37
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

namespace SharpPlanar.Numerical.U37
open IntegerIntervals IntegerBasis IntegerGrid CachedData
lemma entry3_0_contains_g_oai : entry3_0.Contains (umat 3 0) := by
  have h0 := K_column_contains_g (n:=node) (m:=1) (by decide) (by decide) false false cm37_1_0_0.contains
  have h1 := K_column_contains_g (n:=node) (m:=1) (by decide) (by decide) false true cm37_1_0_1.contains
  have hh := S_column_derivative_contains (m:=node1) h0 h1
  change entry3_0.Contains (S (columnVector node false) (node1,true))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  decide +kernel
end SharpPlanar.Numerical.U37

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.U37.entry3_0_contains_g_oai := @OAI.SharpPlanar.Numerical.U37.entry3_0_contains_g_oai
