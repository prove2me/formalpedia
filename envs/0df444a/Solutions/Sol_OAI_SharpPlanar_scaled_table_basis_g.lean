-- Prove2me | solution 1 for OAI.SharpPlanar.scaled_table_basis_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:18:54.966191+00:00
-- url     : https://prove2.me/submissions/260e7749-5576-406c-b7ef-d2d6f0760072

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G396
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

lemma scaled_table_basis_g_oai {a : CBox} {n j : ℕ} {w t : ℝ} {d : Bool}
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

theorem solution : type_of% @OAI.SharpPlanar.scaled_table_basis_g_oai := @OAI.SharpPlanar.scaled_table_basis_g_oai
