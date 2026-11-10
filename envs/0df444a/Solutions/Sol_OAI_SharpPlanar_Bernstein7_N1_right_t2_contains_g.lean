-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein7.N1_right.t2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:57:14.254191+00:00
-- url     : https://prove2.me/submissions/17659f4a-9e05-4782-831d-2c0cc8886716

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G1319
import Definitions.Def_OAIQ098G1330
import Definitions.Def_OAIQ098G1333
import Definitions.Def_OAIQ098G1682
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm7_0_1_4_atomContains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm7_0_1_4_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm7_1_0_4_realContains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel7_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_directMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval enclosures for direct and transformed moments of arbitrary order -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma fullMoment_error (a tr : Bool) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (ell : ℕ) :
    ‖fullMomentIntegral a tr m ell-fullMomentRule a tr m ell‖ < 1/10^22 := by
  cases tr
  · exact directMoment_rule_error_g _ _ (table_range_mass_g a) hm0 hm1 (by norm_num) ell
  · exact transformedMoment_rule_error_g _ _ (table_range_mass_g a) hm0 hm1 (by norm_num) ell
lemma fullMoment_contains {a tr : Bool} {m : ℝ} {ell : ℕ} {ab rb : CBox}
    (ha : ab.Contains (fullMomentAtom a tr m ell))
    (hr : rb.Contains (fullMomentRule a tr m ell)) (hm0 : 0 ≤ m) (hm1 : m ≤ 100) :
    (inflate (ab.add rb).re).Contains (fullMoment a tr m ell) := by
  apply inflate_contains_g (CBox.contains_add_g ha hr).1
  unfold fullMoment
  have he := (Complex.abs_re_le_norm (fullMomentIntegral a tr m ell-fullMomentRule a tr m ell)).trans_lt
    (fullMoment_error a tr hm0 hm1 ell)
  simpa only [Complex.add_re,Complex.sub_re,add_sub_add_left_eq_sub] using he
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighFactorBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval bounds for the normalized Gaussian moment powers -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
lemma momentPower_trans_contains {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains ((lambda t*Complex.exp (Complex.I*Real.pi*z t*m))*1))
    (hb : b.Contains (momentPower ell (z t))) :
    (a.mul b).Contains (complexTransformedFactor m 1 ell t) := by
  have hh := CBox.contains_mul_g ha hb
  simpa only [complexTransformedFactor,Complex.ofReal_one,complexLambda_ofReal_g,
    complexZ_ofReal_g,mul_one,momentPower,mul_div_assoc,Complex.ofReal_natCast] using hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighRuleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian moment bounds at the quadrature nodes and atoms -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
lemma momentPower_trans_full {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains ((lambda t*Complex.exp (Complex.I*Real.pi*z t*m))*1))
    (hb : b.Contains (momentPower ell (z t))) :
    (a.mul b).Contains (fullFactor true m ell t) := by
  simpa only [fullFactor,ite_true, if_true] using momentPower_trans_contains ha hb
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders7
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma hk7_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk7_1_4 j i k).Contains (fullFactor true 7 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk7_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel7_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 7 4 (kernel7_0_contains_g j i k) (mpower1_4_contains_g j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_10
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_1_4
lemma checked : cachedMomentRuleBox density0 hk7_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 7 4) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk7_1_4 (tableDensity false) (fullFactor true 7 4) density0_contains_g hk7_1_4_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 7 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains_g contains (by norm_num) (by norm_num)
end hm7_0_1_4
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein7
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

namespace SharpPlanar.Bernstein7
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma t2_checked : ((hm7_1_0_4.realAnswer).add hm7_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
lemma t2_contains_g_oai : t2.Contains (sourcePower true 7 (1/1) 2 2) := by
  rw [← t2_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm7_1_0_4.realContains_g hm7_0_1_4.realContains) (1) 1 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
end N1_right
end SharpPlanar.Bernstein7

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein7.N1_right.t2_contains_g_oai := @OAI.SharpPlanar.Bernstein7.N1_right.t2_contains_g_oai
