-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm37_0_0_3.realContains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:38:04.981269+00:00
-- url     : https://prove2.me/submissions/7f1efa61-5f00-4ea8-888a-4b58dd5dc9b2

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1168
import Definitions.Def_OAIQ098G1173
import Definitions.Def_OAIQ098G1464
import Definitions.Def_OAIQ098G1682
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm37_0_0_3_atomContains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm37_0_0_3_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power37_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_directMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MomentRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recurrences for the direct and transformed Gaussian moments -/

namespace SharpPlanar
open ComplexConjugate
open IntegerIntervals IntegerBasis
lemma IntegerIntervals.CBox.conj_contains {a : CBox} {z : ℂ} (ha : a.Contains z) :
    a.conj.Contains (conj z) := ⟨ha.1,RBox.neg_contains_g ha.2⟩
lemma direct_factor_zero_contains {a : CBox} {t : ℝ} {m : ℕ}
    (ha : a.Contains (Complex.exp (-Complex.I*Real.pi*t*m))) :
    a.conj.Contains (complexDirectFactor m 1 0 t) := by
  have hh := CBox.conj_contains ha
  rw [← Complex.exp_conj] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [complexDirectFactor,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one]
  congr 1
  simp
lemma factor_step_contains {a b : CBox} {w z : ℂ} (ha : a.Contains w)
    (hb : b.Contains z) (ell : ℕ) :
    ((a.mul b).scale 1 (ell+1)).Contains (w*z/((ell+1:ℕ):ℂ)) := by
  have hh := CBox.contains_scale_g (CBox.contains_mul_g ha hb) 1 (ell+1) (by omega)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast <;> ring)
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
lemma momentPower_step (ell : ℕ) (t : ℂ) :
    momentPower (ell+1) t = momentPower ell t * (Complex.I*Real.pi*t)/((ell+1:ℕ):ℂ) := by
  unfold momentPower
  simp only [pow_succ,Nat.factorial_succ,Nat.cast_mul]
  ring
lemma momentPower_step_contains {a b : CBox} {t : ℂ} {ell : ℕ}
    (ha : a.Contains (momentPower ell t)) (hb : b.Contains (Complex.I*Real.pi*t)) :
    ((a.mul b).scale 1 (ell+1)).Contains (momentPower (ell+1) t) := by
  rw [momentPower_step]
  exact factor_step_contains ha hb ell
lemma momentPower_direct_step_contains (j : Fin 6) (i k : Fin 16) :
    (piI.mul (rcast (gridRows j i k).t)).Contains
      (Complex.I*Real.pi*(quadraturePoint j.val (16*i.val+k.val):ℂ)) := by
  exact CBox.contains_mul_g piI_contains_g (rcast_contains_g (gridRows_contains_g j i k).1)
lemma momentPower_direct_contains {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains (Complex.exp (-Complex.I*Real.pi*t*m)))
    (hb : b.Contains (momentPower ell t)) :
    (a.conj.mul b).Contains (complexDirectFactor m 1 ell t) := by
  have hh := CBox.contains_mul_g (direct_factor_zero_contains ha) hb
  simpa only [complexDirectFactor,Complex.ofReal_one,mul_one,pow_zero,Nat.factorial_zero,
    Nat.cast_one,div_one,momentPower,mul_div_assoc] using hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers5
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
lemma mpower0_3_contains (j : Fin 6) (i k : Fin 16) :
    (mpower0_3 j i k).Contains (momentPower 3 ((quadraturePoint j.val (16*i.val+k.val)))) := by
  rw [← mpower0_3_eq_g]
  exact momentPower_step_contains (mpower0_2_contains_g j i k) (momentPower_direct_step_contains j i k)
end SharpPlanar.CachedData

end OAI
end

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
-- module Solutions.OAIQ098_PP.PlanarPacking_HighRuleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian moment bounds at the quadrature nodes and atoms -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
lemma momentPower_direct_full {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains (Complex.exp (-Complex.I*Real.pi*t*m)))
    (hb : b.Contains (momentPower ell t)) :
    (a.conj.mul b).Contains (fullFactor false m ell t) := by
  simpa only [fullFactor,Bool.false_eq_true,ite_false, if_false] using momentPower_direct_contains ha hb
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders37
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
lemma hk37_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_3 j i k).Contains (fullFactor false 37 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 3 (power37_contains_g j i k) (mpower0_3_contains j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock37_0
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
namespace hm37_0_0_3
lemma checked : cachedMomentRuleBox density0 hk37_0_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 37 3) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk37_0_3 (tableDensity false) (fullFactor false 37 3) density0_contains_g hk37_0_3_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains_g_oai : realAnswer.Contains (fullMoment false false 37 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains_g contains (by norm_num) (by norm_num)
end hm37_0_0_3
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm37_0_0_3.realContains_g_oai := @OAI.SharpPlanar.CachedData.hm37_0_0_3.realContains_g_oai
