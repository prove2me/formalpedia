-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein37.N0_left.tr8_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T22:06:19.755599+00:00
-- url     : https://prove2.me/submissions/32c5a37f-0a15-4dfa-b5fa-3ef9012211cc

import Mathlib
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1697
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_RBox_contains_of_abs_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_mixed_37_10_g
import Theorems.Thm_OAI_SharpPlanar_sharp_moment_bound_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_table_coeff_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_nonneg_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FullMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma fullMoment_transformed (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a true m ell=K (tableData a) ell m/(ell.factorial:ℝ) :=
  tableMomentK_eq_g a m ell
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
lemma table_constant_bound (a : Bool) : |(tableData a).C| ≤ (17:ℝ)/1000 := by
  cases a <;> norm_num [tableData,tableConstant]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MixedTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma fullMoment_transformed_bound (a : Bool) (ell n : ℕ) :
    |fullMoment a true n ell|≤transformTaylor ell n/(ell.factorial:ℝ) := by
  rw [fullMoment_transformed,abs_div,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ)≤(ell.factorial:ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hk:=sharp_moment_bound_g (tableData a) ell (Nat.cast_nonneg n)
  have hm:=table_coeff_mass_g a
  have hc:=table_constant_bound a
  have htn:=transformEnvelope_nonneg_g ell (Nat.cast_nonneg n)
  have han:=atomicEnvelope_nonneg_g ell (n:ℝ)
  have hk1:=mul_le_mul (show |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖≤(23:ℝ)/10 by linarith)
    (transformEnvelope_le_rat_g ell n) htn (by norm_num : (0:ℝ)≤23/10)
  have hk2:=mul_le_mul hc (atomicEnvelope_le_rat_g ell n) han (by norm_num : (0:ℝ)≤17/1000)
  unfold transformTaylor
  exact hk.trans (add_le_add hk1 hk2)
lemma fullMoment_transformed_cap (a : Bool) (ell n : ℕ) {B : ℝ}
    (hB : transformTaylor ell n/(ell.factorial:ℝ)≤B) :
    |fullMoment a true n ell|≤B := (fullMoment_transformed_bound a ell n).trans hB
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein37
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

namespace SharpPlanar.Bernstein37
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_left
lemma tr8_contains_g_oai : tr8.Contains (fullMoment true true 37 10) := by
  apply RBox.contains_of_abs_g (fullMoment_transformed_cap true 10 37 mixed_37_10_g) <;> norm_num [tr8,precision]
end N0_left
end SharpPlanar.Bernstein37

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein37.N0_left.tr8_contains_g_oai := @OAI.SharpPlanar.Bernstein37.N0_left.tr8_contains_g_oai
