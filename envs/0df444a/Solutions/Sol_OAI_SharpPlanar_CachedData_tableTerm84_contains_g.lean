-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm84_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:58:37.730323+00:00
-- url     : https://prove2.me/submissions/3472d29e-f5f5-478d-9ee8-4bf3c8d6de57

import Mathlib
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_column84_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column84_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

lemma tableNum_coefficient (i d : Bool) (n : ℕ) :
    (tableNum i d n:ℝ)/10000000000 = (if d then (tableD i n:ℝ) else (tableC i n:ℝ)) := by
  cases i <;> cases d <;> by_cases hn : n=0 <;>
    simp [tableNum,tableD,tableC,hn] <;> norm_num

lemma scaled_table_basis {a : CBox} {n j : ℕ} {w t : ℝ} {d : Bool}
    (ha : a.Contains ((w:ℂ)*basisFunction d n j t)) (i : Bool) :
    (a.scale (tableNum i d n) 10000000000).Contains
      (((if d then (tableD i n:ℝ) else (tableC i n:ℝ)):ℂ)*((w:ℂ)*basisFunction d n j t)) := by
  have hh := CBox.contains_scale_g ha (tableNum i d n) 10000000000 (by norm_num)
  have hc := congrArg Complex.ofReal (tableNum_coefficient i d n)
  push_cast at hc
  cases d <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hc ⊢ <;>
    rw [← hc] <;> simpa only [Int.cast_ofNat] using hh

end SharpPlanar

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
lemma tableTerm84_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 84 j i k).Contains (((if d then (tableD a 84:ℝ) else (tableC a 84:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 84 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis (column84_0_contains_g j i k) a
  · exact scaled_table_basis (column84_1_contains_g j i k) a
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm84_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm84_contains_g_oai
