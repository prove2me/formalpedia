-- Prove2me | solution 1 for OAI.SharpPlanar.Residual49.bound0_1_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:09:08.41017+00:00
-- url     : https://prove2.me/submissions/df97711a-9c2c-4f57-b435-cc31c2c515ea

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G1666
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1696
import Theorems.Thm_OAI_SharpPlanar_CachedData_tm1_49_0_KContains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tm1_49_1_KContains_g
import Theorems.Thm_OAI_SharpPlanar_D_0_g
import Theorems.Thm_OAI_SharpPlanar_D_1_g
import Theorems.Thm_OAI_SharpPlanar_D_3_g
import Theorems.Thm_OAI_SharpPlanar_D_4_g
import Theorems.Thm_OAI_SharpPlanar_D_7_g
import Theorems.Thm_OAI_SharpPlanar_D_9_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_tableResidual_apply_g

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

end Numerical
end SharpPlanar

end OAI
end

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
lemma tableResidual_deriv (a : Bool) (n : Node) :
    tableResidual a (n,true)=(tableD a n.val:ℝ)+
      (if a=false ∧ n.val=1 then 1 else 0)+
      (tableMomentK (!a) n.val 1-D n.val*tableMomentK (!a) n.val 0)/(Q n.val) := by
  rw [tableResidual_apply_g]
  simp only [transformedJets,ite_true, if_true,and_true,tableMomentK_eq_g,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one]
  ring
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual49
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

namespace SharpPlanar.Residual49
open IntegerIntervals IntegerBasis Numerical CachedData
lemma contains0_1 : box0_1.Contains (tableResidual false (node,true)) := by
  rw [tableResidual_deriv]
  have hv := RBox.contains_rat_g (7495) 10000000000 (by norm_num)
  have hq := qiBox_contains_g 49 (by norm_num [residues])
  have hd := dBox_contains 49 (by norm_num [residues])
  have hh := RBox.contains_add_g hv (RBox.contains_mul_g (RBox.contains_add_g tm1_49_1.KContains_g (RBox.neg_contains_g (RBox.contains_mul_g hd tm1_49_0.KContains_g))) hq)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [box0_1,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg])
lemma bound0_1_g_oai : |tableResidual false (node,true)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains0_1 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
end SharpPlanar.Residual49

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Residual49.bound0_1_g_oai := @OAI.SharpPlanar.Residual49.bound0_1_g_oai
