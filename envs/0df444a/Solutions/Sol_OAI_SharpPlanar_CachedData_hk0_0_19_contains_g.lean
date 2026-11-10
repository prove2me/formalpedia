-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hk0_0_19_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:35:40.011199+00:00
-- url     : https://prove2.me/submissions/a45b5c63-2c78-4c45-91a4-ceb8d8b6eb50

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G426
import Definitions.Def_OAIQ098G1680
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_19_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
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
lemma power0_contains (j : Fin 6) (i k : Fin 16) :
    (power0 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(0:ℕ))) := by
  simpa only [power0,Nat.cast_zero,mul_zero,Complex.exp_zero,Int.cast_one,one_div,inv_one,Int.cast_zero,zero_div,mul_zero,zero_mul,add_zero] using
    (CBox.contains_rat_g 1 1 0 1 (by norm_num) (by norm_num))
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders0
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
lemma hk0_0_19_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (hk0_0_19 j i k).Contains (fullFactor false 0 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 19 (power0_contains j i k) (mpower0_19_contains_g j i k)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hk0_0_19_contains_g_oai := @OAI.SharpPlanar.CachedData.hk0_0_19_contains_g_oai
