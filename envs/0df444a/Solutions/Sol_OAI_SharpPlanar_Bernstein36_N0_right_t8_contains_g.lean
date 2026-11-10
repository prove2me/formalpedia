-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein36.N0_right.t8_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:40:35.926416+00:00
-- url     : https://prove2.me/submissions/2b6cd525-8ff8-46d5-99c0-ff634f863a6d

import Mathlib
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G1164
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1697
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm36_0_0_10_realContains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_RBox_contains_of_abs_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_nonneg_g
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MixedBound36
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
open IntegerIntervals IntegerBasis
lemma mixed_36_10 : transformTaylor 10 36/((Nat.factorial 10):ℝ)≤(102187287443684063655955502:ℝ)/1000000000000000000000000000000 := by
  first | (simp [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein36
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

namespace SharpPlanar.Bernstein36
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
lemma tr8_contains : tr8.Contains (fullMoment true true 36 10) := by
  apply RBox.contains_of_abs_g (fullMoment_transformed_cap true 10 36 mixed_36_10) <;> norm_num [tr8,precision]
lemma t8_checked : ((hm36_0_0_10.realAnswer).add tr8).scale (-1) 256=t8 := by decide +kernel
lemma t8_contains_g_oai : t8.Contains (sourcePower false 36 (1/2) 2 8) := by
  rw [← t8_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm36_0_0_10.realContains_g tr8_contains) (-1) 256 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
end N0_right
end SharpPlanar.Bernstein36

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein36.N0_right.t8_contains_g_oai := @OAI.SharpPlanar.Bernstein36.N0_right.t8_contains_g_oai
