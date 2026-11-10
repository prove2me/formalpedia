-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hk9_1_3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T17:52:35.405506+00:00
-- url     : https://prove2.me/submissions/7d301c33-002f-4ebc-a7af-b504e130857f

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G737
import Definitions.Def_OAIQ098G1481
import Definitions.Def_OAIQ098G1680
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel9_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g

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
lemma momentPower_trans_step_contains (j : Fin 6) (i k : Fin 16) :
    (piI.mul (gridRows j i k).z).Contains
      (Complex.I*Real.pi*(z (quadraturePoint j.val (16*i.val+k.val)))) := by
  have hz := (gridRows_contains_g j i k).2.2.1
  rw [pointZ_eq_g] at hz
  exact CBox.contains_mul_g piI_contains_g hz
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
lemma mpower1_3_contains (j : Fin 6) (i k : Fin 16) :
    (mpower1_3 j i k).Contains (momentPower 3 (z (quadraturePoint j.val (16*i.val+k.val)))) := by
  rw [← mpower1_3_eq_g]
  exact momentPower_step_contains (mpower1_2_contains_g j i k) (momentPower_trans_step_contains j i k)
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
lemma momentPower_trans_full {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains ((lambda t*Complex.exp (Complex.I*Real.pi*z t*m))*1))
    (hb : b.Contains (momentPower ell (z t))) :
    (a.mul b).Contains (fullFactor true m ell t) := by
  simpa only [fullFactor,ite_true, if_true] using momentPower_trans_contains ha hb
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders9
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
lemma hk9_1_3_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (hk9_1_3 j i k).Contains (fullFactor true 9 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk9_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel9_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 9 3 (kernel9_0_contains_g j i k) (mpower1_3_contains j i k)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hk9_1_3_contains_g_oai := @OAI.SharpPlanar.CachedData.hk9_1_3_contains_g_oai
