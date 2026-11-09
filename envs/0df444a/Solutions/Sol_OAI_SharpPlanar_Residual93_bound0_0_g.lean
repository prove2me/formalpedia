-- Prove2me | solution 1 for OAI.SharpPlanar.Residual93.bound0_0_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:31:34.44348+00:00
-- url     : https://prove2.me/submissions/c617b0df-f0ad-4bbf-a2df-66bb11c45e84
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G1668
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1696
import Theorems.Thm_OAI_SharpPlanar_CachedData_tm1_93_0_KContains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_tableResidual_apply_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ResidualBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residuals of the cardinal interpolation equations

The finite coefficient families have small residuals in the exact interpolation equations.
-/

namespace SharpPlanar
open Numerical IntegerIntervals
lemma tableResidual_value (a : Bool) (n : Node) :
    tableResidual a (n,false)=(tableC a n.val:ℝ)+tableMomentK (!a) n.val 0/(Q n.val) := by
  rw [tableResidual_apply_g]
  simp only [transformedJets,Bool.false_eq_true,ite_false, if_false,and_false,tableMomentK_eq_g,
    Nat.factorial_zero,Nat.cast_one,div_one,neg_div,sub_neg_eq_add,add_zero]
lemma RBox.abs_lt {a : RBox} {x : ℝ} {u v : ℤ} (hx : a.Contains x)
    (hv : 0<v) (hc : a.bound*v<precision*u) : |x|<(u:ℝ)/v := by
  have h1 := RBox.abs_bound_g hx
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have h2 : (a.bound:ℝ)*v < (precision:ℝ)*u := by exact_mod_cast hc
  apply (mul_lt_mul_iff_right₀ precision_pos_g).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact (mul_le_mul_of_nonneg_right h1 hv'.le).trans_lt h2
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual93
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

namespace SharpPlanar.Residual93
open IntegerIntervals IntegerBasis Numerical CachedData
lemma contains0_0 : box0_0.Contains (tableResidual false (node,false)) := by
  rw [tableResidual_value]
  have hv := RBox.contains_rat_g (0) 10000000000 (by norm_num)
  have hq := qiBox_contains_g 93 (by norm_num [residues])
  have hh := RBox.contains_add_g hv (RBox.contains_mul_g tm1_93_0.KContains_g hq)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [box0_0,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg])
lemma bound0_0_g_oai : |tableResidual false (node,false)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains0_0 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
end SharpPlanar.Residual93

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Residual93.bound0_0_g_oai := @OAI.SharpPlanar.Residual93.bound0_0_g_oai
