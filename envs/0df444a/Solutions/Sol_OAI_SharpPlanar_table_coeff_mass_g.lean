-- Prove2me | solution 1 for OAI.SharpPlanar.table_coeff_mass_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:20.606444+00:00
-- url     : https://prove2.me/submissions/41fee5e4-1f9d-492c-85e2-9247ba0bdffe

import Mathlib
import Definitions.Def_OAIQ098G010
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1694
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_injective_g
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_norm_g
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g
import Theorems.Thm_OAI_SharpPlanar_tableList_discard_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableList
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

namespace SharpPlanar
open Numerical
lemma tableList_apply (a : Bool) (ni : Node×Bool) :
    tableList a ni = if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ) := rfl
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm bounds for the rational coefficient family

Finite rational sums give bounds for the mass of the cardinal coefficients.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
lemma tableList_norm (a : Bool) : ‖tableList a‖=(tableFiniteNormRat a:ℝ) := by
  have he : tableList a=IF (RF (tableList a)) := sub_eq_zero.mp (tableList_discard_g a)
  calc
    ‖tableList a‖=‖IF (RF (tableList a))‖ := congrArg norm he
    _=‖RF (tableList a)‖ := finiteEmbedding_norm_g finiteIndex finiteIndex_injective_g _
    _=(tableFiniteNormRat a:ℝ) := by
      rw [l1Finite_norm_g]
      simp only [tableFiniteNormRat,Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      change |tableList a (finiteIndex i)|= _
      rw [tableList_apply]
      by_cases hi : (finiteIndex i).2=true <;> simp [tableCoordRat,hi]
lemma table_coeff_mass_g_oai (a : Bool) :
    |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖ < (229:ℝ)/100 := by
  have hr : |tableC a 0|+|tableD a 0|+tableFiniteNormRat a<(229:ℚ)/100 := by
    cases a <;> decide +kernel
  change |(tableC a 0:ℝ)|+|(tableD a 0:ℝ)|+‖tableList a‖ < _
  rw [tableList_norm]
  have hr' : ((|tableC a 0|+|tableD a 0|+tableFiniteNormRat a:ℚ):ℝ)<((229/100:ℚ):ℝ) := Rat.cast_lt.mpr hr
  norm_num only [Rat.cast_add,Rat.cast_abs,Rat.cast_div,Rat.cast_ofNat] at hr'
  exact hr'
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.table_coeff_mass_g_oai := @OAI.SharpPlanar.table_coeff_mass_g_oai
