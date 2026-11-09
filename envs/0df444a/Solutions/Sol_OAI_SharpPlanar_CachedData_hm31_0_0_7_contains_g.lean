-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm31_0_0_7.contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:37:17.136373+00:00
-- url     : https://prove2.me/submissions/0c3e8121-219c-4a54-a9e2-b09d2a3d3458
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G319
import Definitions.Def_OAIQ098G1132
import Definitions.Def_OAIQ098G1134
import Definitions.Def_OAIQ098G1682
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm31_0_0_7_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_7_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power30_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_r5_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
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
lemma power31_r1_0_eq : ∀ k : Fin 16, power31Expr 1 0 k = power31_r1_0 k := by decide +kernel
lemma power31_r1_1_eq : ∀ k : Fin 16, power31Expr 1 1 k = power31_r1_1 k := by decide +kernel
lemma power31_r1_2_eq : ∀ k : Fin 16, power31Expr 1 2 k = power31_r1_2 k := by decide +kernel
lemma power31_r1_3_eq : ∀ k : Fin 16, power31Expr 1 3 k = power31_r1_3 k := by decide +kernel
lemma power31_r1_4_eq : ∀ k : Fin 16, power31Expr 1 4 k = power31_r1_4 k := by decide +kernel
lemma power31_r1_5_eq : ∀ k : Fin 16, power31Expr 1 5 k = power31_r1_5 k := by decide +kernel
lemma power31_r1_6_eq : ∀ k : Fin 16, power31Expr 1 6 k = power31_r1_6 k := by decide +kernel
lemma power31_r1_7_eq : ∀ k : Fin 16, power31Expr 1 7 k = power31_r1_7 k := by decide +kernel
lemma power31_r1_8_eq : ∀ k : Fin 16, power31Expr 1 8 k = power31_r1_8 k := by decide +kernel
lemma power31_r1_9_eq : ∀ k : Fin 16, power31Expr 1 9 k = power31_r1_9 k := by decide +kernel
lemma power31_r1_10_eq : ∀ k : Fin 16, power31Expr 1 10 k = power31_r1_10 k := by decide +kernel
lemma power31_r1_11_eq : ∀ k : Fin 16, power31Expr 1 11 k = power31_r1_11 k := by decide +kernel
lemma power31_r1_12_eq : ∀ k : Fin 16, power31Expr 1 12 k = power31_r1_12 k := by decide +kernel
lemma power31_r1_13_eq : ∀ k : Fin 16, power31Expr 1 13 k = power31_r1_13 k := by decide +kernel
lemma power31_r1_14_eq : ∀ k : Fin 16, power31Expr 1 14 k = power31_r1_14 k := by decide +kernel
lemma power31_r1_15_eq : ∀ k : Fin 16, power31Expr 1 15 k = power31_r1_15 k := by decide +kernel
lemma power31_r1_eq (i k : Fin 16) : power31Expr 1 i k = power31_r1 i k := by
  fin_cases i
  · exact power31_r1_0_eq k
  · exact power31_r1_1_eq k
  · exact power31_r1_2_eq k
  · exact power31_r1_3_eq k
  · exact power31_r1_4_eq k
  · exact power31_r1_5_eq k
  · exact power31_r1_6_eq k
  · exact power31_r1_7_eq k
  · exact power31_r1_8_eq k
  · exact power31_r1_9_eq k
  · exact power31_r1_10_eq k
  · exact power31_r1_11_eq k
  · exact power31_r1_12_eq k
  · exact power31_r1_13_eq k
  · exact power31_r1_14_eq k
  · exact power31_r1_15_eq k
lemma power31_r3_0_eq : ∀ k : Fin 16, power31Expr 3 0 k = power31_r3_0 k := by decide +kernel
lemma power31_r3_1_eq : ∀ k : Fin 16, power31Expr 3 1 k = power31_r3_1 k := by decide +kernel
lemma power31_r3_2_eq : ∀ k : Fin 16, power31Expr 3 2 k = power31_r3_2 k := by decide +kernel
lemma power31_r3_3_eq : ∀ k : Fin 16, power31Expr 3 3 k = power31_r3_3 k := by decide +kernel
lemma power31_r3_4_eq : ∀ k : Fin 16, power31Expr 3 4 k = power31_r3_4 k := by decide +kernel
lemma power31_r3_5_eq : ∀ k : Fin 16, power31Expr 3 5 k = power31_r3_5 k := by decide +kernel
lemma power31_r3_6_eq : ∀ k : Fin 16, power31Expr 3 6 k = power31_r3_6 k := by decide +kernel
lemma power31_r3_7_eq : ∀ k : Fin 16, power31Expr 3 7 k = power31_r3_7 k := by decide +kernel
lemma power31_r3_8_eq : ∀ k : Fin 16, power31Expr 3 8 k = power31_r3_8 k := by decide +kernel
lemma power31_r3_9_eq : ∀ k : Fin 16, power31Expr 3 9 k = power31_r3_9 k := by decide +kernel
lemma power31_r3_10_eq : ∀ k : Fin 16, power31Expr 3 10 k = power31_r3_10 k := by decide +kernel
lemma power31_r3_11_eq : ∀ k : Fin 16, power31Expr 3 11 k = power31_r3_11 k := by decide +kernel
lemma power31_r3_12_eq : ∀ k : Fin 16, power31Expr 3 12 k = power31_r3_12 k := by decide +kernel
lemma power31_r3_13_eq : ∀ k : Fin 16, power31Expr 3 13 k = power31_r3_13 k := by decide +kernel
lemma power31_r3_14_eq : ∀ k : Fin 16, power31Expr 3 14 k = power31_r3_14 k := by decide +kernel
lemma power31_r3_15_eq : ∀ k : Fin 16, power31Expr 3 15 k = power31_r3_15 k := by decide +kernel
lemma power31_r3_eq (i k : Fin 16) : power31Expr 3 i k = power31_r3 i k := by
  fin_cases i
  · exact power31_r3_0_eq k
  · exact power31_r3_1_eq k
  · exact power31_r3_2_eq k
  · exact power31_r3_3_eq k
  · exact power31_r3_4_eq k
  · exact power31_r3_5_eq k
  · exact power31_r3_6_eq k
  · exact power31_r3_7_eq k
  · exact power31_r3_8_eq k
  · exact power31_r3_9_eq k
  · exact power31_r3_10_eq k
  · exact power31_r3_11_eq k
  · exact power31_r3_12_eq k
  · exact power31_r3_13_eq k
  · exact power31_r3_14_eq k
  · exact power31_r3_15_eq k
lemma power31_eq (j : Fin 6) (i k : Fin 16) : power31Expr j i k = power31 j i k := by
  fin_cases j
  · exact power31_r0_eq_g i k
  · exact power31_r1_eq i k
  · exact power31_r2_eq_g i k
  · exact power31_r3_eq i k
  · exact power31_r4_eq_g i k
  · exact power31_r5_eq_g i k
lemma power31_contains (j : Fin 6) (i k : Fin 16) :
    (power31 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(31:ℕ))) := by
  rw [← power31_eq]
  unfold power31Expr
  convert exp_direct_step_g (power30_contains_g j i k) (gridRows_contains_g j i k).2.2.2.1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end SharpPlanar.CachedData

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders31
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
lemma hk31_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_7 j i k).Contains (fullFactor false 31 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 7 (power31_contains j i k) (mpower0_7_contains_g j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock31_0
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
namespace hm31_0_0_7
lemma checked : cachedMomentRuleBox density0 hk31_0_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains_g_oai : ans.Contains (fullMomentRule false false 31 7) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk31_0_7 (tableDensity false) (fullFactor false 31 7) density0_contains_g hk31_0_7_contains
end hm31_0_0_7
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm31_0_0_7.contains_g_oai := @OAI.SharpPlanar.CachedData.hm31_0_0_7.contains_g_oai
