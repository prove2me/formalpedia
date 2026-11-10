-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hk1_0_29_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T09:20:26.798202+00:00
-- url     : https://prove2.me/submissions/ce1da38d-fa36-4561-85d3-48db31b4b1ec

import Mathlib
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G548
import Definitions.Def_OAIQ098G1467
import Definitions.Def_OAIQ098G1680
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_27_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers30
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
lemma mpower0_28_r0_0_eq : ∀ k : Fin 16, mpower0_28Expr 0 0 k = mpower0_28_r0_0 k := by decide +kernel
lemma mpower0_28_r0_1_eq : ∀ k : Fin 16, mpower0_28Expr 0 1 k = mpower0_28_r0_1 k := by decide +kernel
lemma mpower0_28_r0_2_eq : ∀ k : Fin 16, mpower0_28Expr 0 2 k = mpower0_28_r0_2 k := by decide +kernel
lemma mpower0_28_r0_3_eq : ∀ k : Fin 16, mpower0_28Expr 0 3 k = mpower0_28_r0_3 k := by decide +kernel
lemma mpower0_28_r0_4_eq : ∀ k : Fin 16, mpower0_28Expr 0 4 k = mpower0_28_r0_4 k := by decide +kernel
lemma mpower0_28_r0_5_eq : ∀ k : Fin 16, mpower0_28Expr 0 5 k = mpower0_28_r0_5 k := by decide +kernel
lemma mpower0_28_r0_6_eq : ∀ k : Fin 16, mpower0_28Expr 0 6 k = mpower0_28_r0_6 k := by decide +kernel
lemma mpower0_28_r0_7_eq : ∀ k : Fin 16, mpower0_28Expr 0 7 k = mpower0_28_r0_7 k := by decide +kernel
lemma mpower0_28_r0_8_eq : ∀ k : Fin 16, mpower0_28Expr 0 8 k = mpower0_28_r0_8 k := by decide +kernel
lemma mpower0_28_r0_9_eq : ∀ k : Fin 16, mpower0_28Expr 0 9 k = mpower0_28_r0_9 k := by decide +kernel
lemma mpower0_28_r0_10_eq : ∀ k : Fin 16, mpower0_28Expr 0 10 k = mpower0_28_r0_10 k := by decide +kernel
lemma mpower0_28_r0_11_eq : ∀ k : Fin 16, mpower0_28Expr 0 11 k = mpower0_28_r0_11 k := by decide +kernel
lemma mpower0_28_r0_12_eq : ∀ k : Fin 16, mpower0_28Expr 0 12 k = mpower0_28_r0_12 k := by decide +kernel
lemma mpower0_28_r0_13_eq : ∀ k : Fin 16, mpower0_28Expr 0 13 k = mpower0_28_r0_13 k := by decide +kernel
lemma mpower0_28_r0_14_eq : ∀ k : Fin 16, mpower0_28Expr 0 14 k = mpower0_28_r0_14 k := by decide +kernel
lemma mpower0_28_r0_15_eq : ∀ k : Fin 16, mpower0_28Expr 0 15 k = mpower0_28_r0_15 k := by decide +kernel
lemma mpower0_28_r0_eq (i k : Fin 16) : mpower0_28Expr 0 i k = mpower0_28_r0 i k := by
  fin_cases i
  · exact mpower0_28_r0_0_eq k
  · exact mpower0_28_r0_1_eq k
  · exact mpower0_28_r0_2_eq k
  · exact mpower0_28_r0_3_eq k
  · exact mpower0_28_r0_4_eq k
  · exact mpower0_28_r0_5_eq k
  · exact mpower0_28_r0_6_eq k
  · exact mpower0_28_r0_7_eq k
  · exact mpower0_28_r0_8_eq k
  · exact mpower0_28_r0_9_eq k
  · exact mpower0_28_r0_10_eq k
  · exact mpower0_28_r0_11_eq k
  · exact mpower0_28_r0_12_eq k
  · exact mpower0_28_r0_13_eq k
  · exact mpower0_28_r0_14_eq k
  · exact mpower0_28_r0_15_eq k
lemma mpower0_28_r1_0_eq : ∀ k : Fin 16, mpower0_28Expr 1 0 k = mpower0_28_r1_0 k := by decide +kernel
lemma mpower0_28_r1_1_eq : ∀ k : Fin 16, mpower0_28Expr 1 1 k = mpower0_28_r1_1 k := by decide +kernel
lemma mpower0_28_r1_2_eq : ∀ k : Fin 16, mpower0_28Expr 1 2 k = mpower0_28_r1_2 k := by decide +kernel
lemma mpower0_28_r1_3_eq : ∀ k : Fin 16, mpower0_28Expr 1 3 k = mpower0_28_r1_3 k := by decide +kernel
lemma mpower0_28_r1_4_eq : ∀ k : Fin 16, mpower0_28Expr 1 4 k = mpower0_28_r1_4 k := by decide +kernel
lemma mpower0_28_r1_5_eq : ∀ k : Fin 16, mpower0_28Expr 1 5 k = mpower0_28_r1_5 k := by decide +kernel
lemma mpower0_28_r1_6_eq : ∀ k : Fin 16, mpower0_28Expr 1 6 k = mpower0_28_r1_6 k := by decide +kernel
lemma mpower0_28_r1_7_eq : ∀ k : Fin 16, mpower0_28Expr 1 7 k = mpower0_28_r1_7 k := by decide +kernel
lemma mpower0_28_r1_8_eq : ∀ k : Fin 16, mpower0_28Expr 1 8 k = mpower0_28_r1_8 k := by decide +kernel
lemma mpower0_28_r1_9_eq : ∀ k : Fin 16, mpower0_28Expr 1 9 k = mpower0_28_r1_9 k := by decide +kernel
lemma mpower0_28_r1_10_eq : ∀ k : Fin 16, mpower0_28Expr 1 10 k = mpower0_28_r1_10 k := by decide +kernel
lemma mpower0_28_r1_11_eq : ∀ k : Fin 16, mpower0_28Expr 1 11 k = mpower0_28_r1_11 k := by decide +kernel
lemma mpower0_28_r1_12_eq : ∀ k : Fin 16, mpower0_28Expr 1 12 k = mpower0_28_r1_12 k := by decide +kernel
lemma mpower0_28_r1_13_eq : ∀ k : Fin 16, mpower0_28Expr 1 13 k = mpower0_28_r1_13 k := by decide +kernel
lemma mpower0_28_r1_14_eq : ∀ k : Fin 16, mpower0_28Expr 1 14 k = mpower0_28_r1_14 k := by decide +kernel
lemma mpower0_28_r1_15_eq : ∀ k : Fin 16, mpower0_28Expr 1 15 k = mpower0_28_r1_15 k := by decide +kernel
lemma mpower0_28_r1_eq (i k : Fin 16) : mpower0_28Expr 1 i k = mpower0_28_r1 i k := by
  fin_cases i
  · exact mpower0_28_r1_0_eq k
  · exact mpower0_28_r1_1_eq k
  · exact mpower0_28_r1_2_eq k
  · exact mpower0_28_r1_3_eq k
  · exact mpower0_28_r1_4_eq k
  · exact mpower0_28_r1_5_eq k
  · exact mpower0_28_r1_6_eq k
  · exact mpower0_28_r1_7_eq k
  · exact mpower0_28_r1_8_eq k
  · exact mpower0_28_r1_9_eq k
  · exact mpower0_28_r1_10_eq k
  · exact mpower0_28_r1_11_eq k
  · exact mpower0_28_r1_12_eq k
  · exact mpower0_28_r1_13_eq k
  · exact mpower0_28_r1_14_eq k
  · exact mpower0_28_r1_15_eq k
lemma mpower0_28_r2_0_eq : ∀ k : Fin 16, mpower0_28Expr 2 0 k = mpower0_28_r2_0 k := by decide +kernel
lemma mpower0_28_r2_1_eq : ∀ k : Fin 16, mpower0_28Expr 2 1 k = mpower0_28_r2_1 k := by decide +kernel
lemma mpower0_28_r2_2_eq : ∀ k : Fin 16, mpower0_28Expr 2 2 k = mpower0_28_r2_2 k := by decide +kernel
lemma mpower0_28_r2_3_eq : ∀ k : Fin 16, mpower0_28Expr 2 3 k = mpower0_28_r2_3 k := by decide +kernel
lemma mpower0_28_r2_4_eq : ∀ k : Fin 16, mpower0_28Expr 2 4 k = mpower0_28_r2_4 k := by decide +kernel
lemma mpower0_28_r2_5_eq : ∀ k : Fin 16, mpower0_28Expr 2 5 k = mpower0_28_r2_5 k := by decide +kernel
lemma mpower0_28_r2_6_eq : ∀ k : Fin 16, mpower0_28Expr 2 6 k = mpower0_28_r2_6 k := by decide +kernel
lemma mpower0_28_r2_7_eq : ∀ k : Fin 16, mpower0_28Expr 2 7 k = mpower0_28_r2_7 k := by decide +kernel
lemma mpower0_28_r2_8_eq : ∀ k : Fin 16, mpower0_28Expr 2 8 k = mpower0_28_r2_8 k := by decide +kernel
lemma mpower0_28_r2_9_eq : ∀ k : Fin 16, mpower0_28Expr 2 9 k = mpower0_28_r2_9 k := by decide +kernel
lemma mpower0_28_r2_10_eq : ∀ k : Fin 16, mpower0_28Expr 2 10 k = mpower0_28_r2_10 k := by decide +kernel
lemma mpower0_28_r2_11_eq : ∀ k : Fin 16, mpower0_28Expr 2 11 k = mpower0_28_r2_11 k := by decide +kernel
lemma mpower0_28_r2_12_eq : ∀ k : Fin 16, mpower0_28Expr 2 12 k = mpower0_28_r2_12 k := by decide +kernel
lemma mpower0_28_r2_13_eq : ∀ k : Fin 16, mpower0_28Expr 2 13 k = mpower0_28_r2_13 k := by decide +kernel
lemma mpower0_28_r2_14_eq : ∀ k : Fin 16, mpower0_28Expr 2 14 k = mpower0_28_r2_14 k := by decide +kernel
lemma mpower0_28_r2_15_eq : ∀ k : Fin 16, mpower0_28Expr 2 15 k = mpower0_28_r2_15 k := by decide +kernel
lemma mpower0_28_r2_eq (i k : Fin 16) : mpower0_28Expr 2 i k = mpower0_28_r2 i k := by
  fin_cases i
  · exact mpower0_28_r2_0_eq k
  · exact mpower0_28_r2_1_eq k
  · exact mpower0_28_r2_2_eq k
  · exact mpower0_28_r2_3_eq k
  · exact mpower0_28_r2_4_eq k
  · exact mpower0_28_r2_5_eq k
  · exact mpower0_28_r2_6_eq k
  · exact mpower0_28_r2_7_eq k
  · exact mpower0_28_r2_8_eq k
  · exact mpower0_28_r2_9_eq k
  · exact mpower0_28_r2_10_eq k
  · exact mpower0_28_r2_11_eq k
  · exact mpower0_28_r2_12_eq k
  · exact mpower0_28_r2_13_eq k
  · exact mpower0_28_r2_14_eq k
  · exact mpower0_28_r2_15_eq k
lemma mpower0_28_r3_0_eq : ∀ k : Fin 16, mpower0_28Expr 3 0 k = mpower0_28_r3_0 k := by decide +kernel
lemma mpower0_28_r3_1_eq : ∀ k : Fin 16, mpower0_28Expr 3 1 k = mpower0_28_r3_1 k := by decide +kernel
lemma mpower0_28_r3_2_eq : ∀ k : Fin 16, mpower0_28Expr 3 2 k = mpower0_28_r3_2 k := by decide +kernel
lemma mpower0_28_r3_3_eq : ∀ k : Fin 16, mpower0_28Expr 3 3 k = mpower0_28_r3_3 k := by decide +kernel
lemma mpower0_28_r3_4_eq : ∀ k : Fin 16, mpower0_28Expr 3 4 k = mpower0_28_r3_4 k := by decide +kernel
lemma mpower0_28_r3_5_eq : ∀ k : Fin 16, mpower0_28Expr 3 5 k = mpower0_28_r3_5 k := by decide +kernel
lemma mpower0_28_r3_6_eq : ∀ k : Fin 16, mpower0_28Expr 3 6 k = mpower0_28_r3_6 k := by decide +kernel
lemma mpower0_28_r3_7_eq : ∀ k : Fin 16, mpower0_28Expr 3 7 k = mpower0_28_r3_7 k := by decide +kernel
lemma mpower0_28_r3_8_eq : ∀ k : Fin 16, mpower0_28Expr 3 8 k = mpower0_28_r3_8 k := by decide +kernel
lemma mpower0_28_r3_9_eq : ∀ k : Fin 16, mpower0_28Expr 3 9 k = mpower0_28_r3_9 k := by decide +kernel
lemma mpower0_28_r3_10_eq : ∀ k : Fin 16, mpower0_28Expr 3 10 k = mpower0_28_r3_10 k := by decide +kernel
lemma mpower0_28_r3_11_eq : ∀ k : Fin 16, mpower0_28Expr 3 11 k = mpower0_28_r3_11 k := by decide +kernel
lemma mpower0_28_r3_12_eq : ∀ k : Fin 16, mpower0_28Expr 3 12 k = mpower0_28_r3_12 k := by decide +kernel
lemma mpower0_28_r3_13_eq : ∀ k : Fin 16, mpower0_28Expr 3 13 k = mpower0_28_r3_13 k := by decide +kernel
lemma mpower0_28_r3_14_eq : ∀ k : Fin 16, mpower0_28Expr 3 14 k = mpower0_28_r3_14 k := by decide +kernel
lemma mpower0_28_r3_15_eq : ∀ k : Fin 16, mpower0_28Expr 3 15 k = mpower0_28_r3_15 k := by decide +kernel
lemma mpower0_28_r3_eq (i k : Fin 16) : mpower0_28Expr 3 i k = mpower0_28_r3 i k := by
  fin_cases i
  · exact mpower0_28_r3_0_eq k
  · exact mpower0_28_r3_1_eq k
  · exact mpower0_28_r3_2_eq k
  · exact mpower0_28_r3_3_eq k
  · exact mpower0_28_r3_4_eq k
  · exact mpower0_28_r3_5_eq k
  · exact mpower0_28_r3_6_eq k
  · exact mpower0_28_r3_7_eq k
  · exact mpower0_28_r3_8_eq k
  · exact mpower0_28_r3_9_eq k
  · exact mpower0_28_r3_10_eq k
  · exact mpower0_28_r3_11_eq k
  · exact mpower0_28_r3_12_eq k
  · exact mpower0_28_r3_13_eq k
  · exact mpower0_28_r3_14_eq k
  · exact mpower0_28_r3_15_eq k
lemma mpower0_28_r4_0_eq : ∀ k : Fin 16, mpower0_28Expr 4 0 k = mpower0_28_r4_0 k := by decide +kernel
lemma mpower0_28_r4_1_eq : ∀ k : Fin 16, mpower0_28Expr 4 1 k = mpower0_28_r4_1 k := by decide +kernel
lemma mpower0_28_r4_2_eq : ∀ k : Fin 16, mpower0_28Expr 4 2 k = mpower0_28_r4_2 k := by decide +kernel
lemma mpower0_28_r4_3_eq : ∀ k : Fin 16, mpower0_28Expr 4 3 k = mpower0_28_r4_3 k := by decide +kernel
lemma mpower0_28_r4_4_eq : ∀ k : Fin 16, mpower0_28Expr 4 4 k = mpower0_28_r4_4 k := by decide +kernel
lemma mpower0_28_r4_5_eq : ∀ k : Fin 16, mpower0_28Expr 4 5 k = mpower0_28_r4_5 k := by decide +kernel
lemma mpower0_28_r4_6_eq : ∀ k : Fin 16, mpower0_28Expr 4 6 k = mpower0_28_r4_6 k := by decide +kernel
lemma mpower0_28_r4_7_eq : ∀ k : Fin 16, mpower0_28Expr 4 7 k = mpower0_28_r4_7 k := by decide +kernel
lemma mpower0_28_r4_8_eq : ∀ k : Fin 16, mpower0_28Expr 4 8 k = mpower0_28_r4_8 k := by decide +kernel
lemma mpower0_28_r4_9_eq : ∀ k : Fin 16, mpower0_28Expr 4 9 k = mpower0_28_r4_9 k := by decide +kernel
lemma mpower0_28_r4_10_eq : ∀ k : Fin 16, mpower0_28Expr 4 10 k = mpower0_28_r4_10 k := by decide +kernel
lemma mpower0_28_r4_11_eq : ∀ k : Fin 16, mpower0_28Expr 4 11 k = mpower0_28_r4_11 k := by decide +kernel
lemma mpower0_28_r4_12_eq : ∀ k : Fin 16, mpower0_28Expr 4 12 k = mpower0_28_r4_12 k := by decide +kernel
lemma mpower0_28_r4_13_eq : ∀ k : Fin 16, mpower0_28Expr 4 13 k = mpower0_28_r4_13 k := by decide +kernel
lemma mpower0_28_r4_14_eq : ∀ k : Fin 16, mpower0_28Expr 4 14 k = mpower0_28_r4_14 k := by decide +kernel
lemma mpower0_28_r4_15_eq : ∀ k : Fin 16, mpower0_28Expr 4 15 k = mpower0_28_r4_15 k := by decide +kernel
lemma mpower0_28_r4_eq (i k : Fin 16) : mpower0_28Expr 4 i k = mpower0_28_r4 i k := by
  fin_cases i
  · exact mpower0_28_r4_0_eq k
  · exact mpower0_28_r4_1_eq k
  · exact mpower0_28_r4_2_eq k
  · exact mpower0_28_r4_3_eq k
  · exact mpower0_28_r4_4_eq k
  · exact mpower0_28_r4_5_eq k
  · exact mpower0_28_r4_6_eq k
  · exact mpower0_28_r4_7_eq k
  · exact mpower0_28_r4_8_eq k
  · exact mpower0_28_r4_9_eq k
  · exact mpower0_28_r4_10_eq k
  · exact mpower0_28_r4_11_eq k
  · exact mpower0_28_r4_12_eq k
  · exact mpower0_28_r4_13_eq k
  · exact mpower0_28_r4_14_eq k
  · exact mpower0_28_r4_15_eq k
lemma mpower0_28_r5_0_eq : ∀ k : Fin 16, mpower0_28Expr 5 0 k = mpower0_28_r5_0 k := by decide +kernel
lemma mpower0_28_r5_1_eq : ∀ k : Fin 16, mpower0_28Expr 5 1 k = mpower0_28_r5_1 k := by decide +kernel
lemma mpower0_28_r5_2_eq : ∀ k : Fin 16, mpower0_28Expr 5 2 k = mpower0_28_r5_2 k := by decide +kernel
lemma mpower0_28_r5_3_eq : ∀ k : Fin 16, mpower0_28Expr 5 3 k = mpower0_28_r5_3 k := by decide +kernel
lemma mpower0_28_r5_4_eq : ∀ k : Fin 16, mpower0_28Expr 5 4 k = mpower0_28_r5_4 k := by decide +kernel
lemma mpower0_28_r5_5_eq : ∀ k : Fin 16, mpower0_28Expr 5 5 k = mpower0_28_r5_5 k := by decide +kernel
lemma mpower0_28_r5_6_eq : ∀ k : Fin 16, mpower0_28Expr 5 6 k = mpower0_28_r5_6 k := by decide +kernel
lemma mpower0_28_r5_7_eq : ∀ k : Fin 16, mpower0_28Expr 5 7 k = mpower0_28_r5_7 k := by decide +kernel
lemma mpower0_28_r5_8_eq : ∀ k : Fin 16, mpower0_28Expr 5 8 k = mpower0_28_r5_8 k := by decide +kernel
lemma mpower0_28_r5_9_eq : ∀ k : Fin 16, mpower0_28Expr 5 9 k = mpower0_28_r5_9 k := by decide +kernel
lemma mpower0_28_r5_10_eq : ∀ k : Fin 16, mpower0_28Expr 5 10 k = mpower0_28_r5_10 k := by decide +kernel
lemma mpower0_28_r5_11_eq : ∀ k : Fin 16, mpower0_28Expr 5 11 k = mpower0_28_r5_11 k := by decide +kernel
lemma mpower0_28_r5_12_eq : ∀ k : Fin 16, mpower0_28Expr 5 12 k = mpower0_28_r5_12 k := by decide +kernel
lemma mpower0_28_r5_13_eq : ∀ k : Fin 16, mpower0_28Expr 5 13 k = mpower0_28_r5_13 k := by decide +kernel
lemma mpower0_28_r5_14_eq : ∀ k : Fin 16, mpower0_28Expr 5 14 k = mpower0_28_r5_14 k := by decide +kernel
lemma mpower0_28_r5_15_eq : ∀ k : Fin 16, mpower0_28Expr 5 15 k = mpower0_28_r5_15 k := by decide +kernel
lemma mpower0_28_r5_eq (i k : Fin 16) : mpower0_28Expr 5 i k = mpower0_28_r5 i k := by
  fin_cases i
  · exact mpower0_28_r5_0_eq k
  · exact mpower0_28_r5_1_eq k
  · exact mpower0_28_r5_2_eq k
  · exact mpower0_28_r5_3_eq k
  · exact mpower0_28_r5_4_eq k
  · exact mpower0_28_r5_5_eq k
  · exact mpower0_28_r5_6_eq k
  · exact mpower0_28_r5_7_eq k
  · exact mpower0_28_r5_8_eq k
  · exact mpower0_28_r5_9_eq k
  · exact mpower0_28_r5_10_eq k
  · exact mpower0_28_r5_11_eq k
  · exact mpower0_28_r5_12_eq k
  · exact mpower0_28_r5_13_eq k
  · exact mpower0_28_r5_14_eq k
  · exact mpower0_28_r5_15_eq k
lemma mpower0_28_eq (j : Fin 6) (i k : Fin 16) : mpower0_28Expr j i k = mpower0_28 j i k := by
  fin_cases j
  · exact mpower0_28_r0_eq i k
  · exact mpower0_28_r1_eq i k
  · exact mpower0_28_r2_eq i k
  · exact mpower0_28_r3_eq i k
  · exact mpower0_28_r4_eq i k
  · exact mpower0_28_r5_eq i k
lemma mpower0_28_contains (j : Fin 6) (i k : Fin 16) :
    (mpower0_28 j i k).Contains (momentPower 28 ((quadraturePoint j.val (16*i.val+k.val)))) := by
  rw [← mpower0_28_eq]
  exact momentPower_step_contains (mpower0_27_contains_g j i k) (momentPower_direct_step_contains j i k)
lemma mpower0_29_r0_0_eq : ∀ k : Fin 16, mpower0_29Expr 0 0 k = mpower0_29_r0_0 k := by decide +kernel
lemma mpower0_29_r0_1_eq : ∀ k : Fin 16, mpower0_29Expr 0 1 k = mpower0_29_r0_1 k := by decide +kernel
lemma mpower0_29_r0_2_eq : ∀ k : Fin 16, mpower0_29Expr 0 2 k = mpower0_29_r0_2 k := by decide +kernel
lemma mpower0_29_r0_3_eq : ∀ k : Fin 16, mpower0_29Expr 0 3 k = mpower0_29_r0_3 k := by decide +kernel
lemma mpower0_29_r0_4_eq : ∀ k : Fin 16, mpower0_29Expr 0 4 k = mpower0_29_r0_4 k := by decide +kernel
lemma mpower0_29_r0_5_eq : ∀ k : Fin 16, mpower0_29Expr 0 5 k = mpower0_29_r0_5 k := by decide +kernel
lemma mpower0_29_r0_6_eq : ∀ k : Fin 16, mpower0_29Expr 0 6 k = mpower0_29_r0_6 k := by decide +kernel
lemma mpower0_29_r0_7_eq : ∀ k : Fin 16, mpower0_29Expr 0 7 k = mpower0_29_r0_7 k := by decide +kernel
lemma mpower0_29_r0_8_eq : ∀ k : Fin 16, mpower0_29Expr 0 8 k = mpower0_29_r0_8 k := by decide +kernel
lemma mpower0_29_r0_9_eq : ∀ k : Fin 16, mpower0_29Expr 0 9 k = mpower0_29_r0_9 k := by decide +kernel
lemma mpower0_29_r0_10_eq : ∀ k : Fin 16, mpower0_29Expr 0 10 k = mpower0_29_r0_10 k := by decide +kernel
lemma mpower0_29_r0_11_eq : ∀ k : Fin 16, mpower0_29Expr 0 11 k = mpower0_29_r0_11 k := by decide +kernel
lemma mpower0_29_r0_12_eq : ∀ k : Fin 16, mpower0_29Expr 0 12 k = mpower0_29_r0_12 k := by decide +kernel
lemma mpower0_29_r0_13_eq : ∀ k : Fin 16, mpower0_29Expr 0 13 k = mpower0_29_r0_13 k := by decide +kernel
lemma mpower0_29_r0_14_eq : ∀ k : Fin 16, mpower0_29Expr 0 14 k = mpower0_29_r0_14 k := by decide +kernel
lemma mpower0_29_r0_15_eq : ∀ k : Fin 16, mpower0_29Expr 0 15 k = mpower0_29_r0_15 k := by decide +kernel
lemma mpower0_29_r0_eq (i k : Fin 16) : mpower0_29Expr 0 i k = mpower0_29_r0 i k := by
  fin_cases i
  · exact mpower0_29_r0_0_eq k
  · exact mpower0_29_r0_1_eq k
  · exact mpower0_29_r0_2_eq k
  · exact mpower0_29_r0_3_eq k
  · exact mpower0_29_r0_4_eq k
  · exact mpower0_29_r0_5_eq k
  · exact mpower0_29_r0_6_eq k
  · exact mpower0_29_r0_7_eq k
  · exact mpower0_29_r0_8_eq k
  · exact mpower0_29_r0_9_eq k
  · exact mpower0_29_r0_10_eq k
  · exact mpower0_29_r0_11_eq k
  · exact mpower0_29_r0_12_eq k
  · exact mpower0_29_r0_13_eq k
  · exact mpower0_29_r0_14_eq k
  · exact mpower0_29_r0_15_eq k
lemma mpower0_29_r1_0_eq : ∀ k : Fin 16, mpower0_29Expr 1 0 k = mpower0_29_r1_0 k := by decide +kernel
lemma mpower0_29_r1_1_eq : ∀ k : Fin 16, mpower0_29Expr 1 1 k = mpower0_29_r1_1 k := by decide +kernel
lemma mpower0_29_r1_2_eq : ∀ k : Fin 16, mpower0_29Expr 1 2 k = mpower0_29_r1_2 k := by decide +kernel
lemma mpower0_29_r1_3_eq : ∀ k : Fin 16, mpower0_29Expr 1 3 k = mpower0_29_r1_3 k := by decide +kernel
lemma mpower0_29_r1_4_eq : ∀ k : Fin 16, mpower0_29Expr 1 4 k = mpower0_29_r1_4 k := by decide +kernel
lemma mpower0_29_r1_5_eq : ∀ k : Fin 16, mpower0_29Expr 1 5 k = mpower0_29_r1_5 k := by decide +kernel
lemma mpower0_29_r1_6_eq : ∀ k : Fin 16, mpower0_29Expr 1 6 k = mpower0_29_r1_6 k := by decide +kernel
lemma mpower0_29_r1_7_eq : ∀ k : Fin 16, mpower0_29Expr 1 7 k = mpower0_29_r1_7 k := by decide +kernel
lemma mpower0_29_r1_8_eq : ∀ k : Fin 16, mpower0_29Expr 1 8 k = mpower0_29_r1_8 k := by decide +kernel
lemma mpower0_29_r1_9_eq : ∀ k : Fin 16, mpower0_29Expr 1 9 k = mpower0_29_r1_9 k := by decide +kernel
lemma mpower0_29_r1_10_eq : ∀ k : Fin 16, mpower0_29Expr 1 10 k = mpower0_29_r1_10 k := by decide +kernel
lemma mpower0_29_r1_11_eq : ∀ k : Fin 16, mpower0_29Expr 1 11 k = mpower0_29_r1_11 k := by decide +kernel
lemma mpower0_29_r1_12_eq : ∀ k : Fin 16, mpower0_29Expr 1 12 k = mpower0_29_r1_12 k := by decide +kernel
lemma mpower0_29_r1_13_eq : ∀ k : Fin 16, mpower0_29Expr 1 13 k = mpower0_29_r1_13 k := by decide +kernel
lemma mpower0_29_r1_14_eq : ∀ k : Fin 16, mpower0_29Expr 1 14 k = mpower0_29_r1_14 k := by decide +kernel
lemma mpower0_29_r1_15_eq : ∀ k : Fin 16, mpower0_29Expr 1 15 k = mpower0_29_r1_15 k := by decide +kernel
lemma mpower0_29_r1_eq (i k : Fin 16) : mpower0_29Expr 1 i k = mpower0_29_r1 i k := by
  fin_cases i
  · exact mpower0_29_r1_0_eq k
  · exact mpower0_29_r1_1_eq k
  · exact mpower0_29_r1_2_eq k
  · exact mpower0_29_r1_3_eq k
  · exact mpower0_29_r1_4_eq k
  · exact mpower0_29_r1_5_eq k
  · exact mpower0_29_r1_6_eq k
  · exact mpower0_29_r1_7_eq k
  · exact mpower0_29_r1_8_eq k
  · exact mpower0_29_r1_9_eq k
  · exact mpower0_29_r1_10_eq k
  · exact mpower0_29_r1_11_eq k
  · exact mpower0_29_r1_12_eq k
  · exact mpower0_29_r1_13_eq k
  · exact mpower0_29_r1_14_eq k
  · exact mpower0_29_r1_15_eq k
lemma mpower0_29_r2_0_eq : ∀ k : Fin 16, mpower0_29Expr 2 0 k = mpower0_29_r2_0 k := by decide +kernel
lemma mpower0_29_r2_1_eq : ∀ k : Fin 16, mpower0_29Expr 2 1 k = mpower0_29_r2_1 k := by decide +kernel
lemma mpower0_29_r2_2_eq : ∀ k : Fin 16, mpower0_29Expr 2 2 k = mpower0_29_r2_2 k := by decide +kernel
lemma mpower0_29_r2_3_eq : ∀ k : Fin 16, mpower0_29Expr 2 3 k = mpower0_29_r2_3 k := by decide +kernel
lemma mpower0_29_r2_4_eq : ∀ k : Fin 16, mpower0_29Expr 2 4 k = mpower0_29_r2_4 k := by decide +kernel
lemma mpower0_29_r2_5_eq : ∀ k : Fin 16, mpower0_29Expr 2 5 k = mpower0_29_r2_5 k := by decide +kernel
lemma mpower0_29_r2_6_eq : ∀ k : Fin 16, mpower0_29Expr 2 6 k = mpower0_29_r2_6 k := by decide +kernel
lemma mpower0_29_r2_7_eq : ∀ k : Fin 16, mpower0_29Expr 2 7 k = mpower0_29_r2_7 k := by decide +kernel
lemma mpower0_29_r2_8_eq : ∀ k : Fin 16, mpower0_29Expr 2 8 k = mpower0_29_r2_8 k := by decide +kernel
lemma mpower0_29_r2_9_eq : ∀ k : Fin 16, mpower0_29Expr 2 9 k = mpower0_29_r2_9 k := by decide +kernel
lemma mpower0_29_r2_10_eq : ∀ k : Fin 16, mpower0_29Expr 2 10 k = mpower0_29_r2_10 k := by decide +kernel
lemma mpower0_29_r2_11_eq : ∀ k : Fin 16, mpower0_29Expr 2 11 k = mpower0_29_r2_11 k := by decide +kernel
lemma mpower0_29_r2_12_eq : ∀ k : Fin 16, mpower0_29Expr 2 12 k = mpower0_29_r2_12 k := by decide +kernel
lemma mpower0_29_r2_13_eq : ∀ k : Fin 16, mpower0_29Expr 2 13 k = mpower0_29_r2_13 k := by decide +kernel
lemma mpower0_29_r2_14_eq : ∀ k : Fin 16, mpower0_29Expr 2 14 k = mpower0_29_r2_14 k := by decide +kernel
lemma mpower0_29_r2_15_eq : ∀ k : Fin 16, mpower0_29Expr 2 15 k = mpower0_29_r2_15 k := by decide +kernel
lemma mpower0_29_r2_eq (i k : Fin 16) : mpower0_29Expr 2 i k = mpower0_29_r2 i k := by
  fin_cases i
  · exact mpower0_29_r2_0_eq k
  · exact mpower0_29_r2_1_eq k
  · exact mpower0_29_r2_2_eq k
  · exact mpower0_29_r2_3_eq k
  · exact mpower0_29_r2_4_eq k
  · exact mpower0_29_r2_5_eq k
  · exact mpower0_29_r2_6_eq k
  · exact mpower0_29_r2_7_eq k
  · exact mpower0_29_r2_8_eq k
  · exact mpower0_29_r2_9_eq k
  · exact mpower0_29_r2_10_eq k
  · exact mpower0_29_r2_11_eq k
  · exact mpower0_29_r2_12_eq k
  · exact mpower0_29_r2_13_eq k
  · exact mpower0_29_r2_14_eq k
  · exact mpower0_29_r2_15_eq k
lemma mpower0_29_r3_0_eq : ∀ k : Fin 16, mpower0_29Expr 3 0 k = mpower0_29_r3_0 k := by decide +kernel
lemma mpower0_29_r3_1_eq : ∀ k : Fin 16, mpower0_29Expr 3 1 k = mpower0_29_r3_1 k := by decide +kernel
lemma mpower0_29_r3_2_eq : ∀ k : Fin 16, mpower0_29Expr 3 2 k = mpower0_29_r3_2 k := by decide +kernel
lemma mpower0_29_r3_3_eq : ∀ k : Fin 16, mpower0_29Expr 3 3 k = mpower0_29_r3_3 k := by decide +kernel
lemma mpower0_29_r3_4_eq : ∀ k : Fin 16, mpower0_29Expr 3 4 k = mpower0_29_r3_4 k := by decide +kernel
lemma mpower0_29_r3_5_eq : ∀ k : Fin 16, mpower0_29Expr 3 5 k = mpower0_29_r3_5 k := by decide +kernel
lemma mpower0_29_r3_6_eq : ∀ k : Fin 16, mpower0_29Expr 3 6 k = mpower0_29_r3_6 k := by decide +kernel
lemma mpower0_29_r3_7_eq : ∀ k : Fin 16, mpower0_29Expr 3 7 k = mpower0_29_r3_7 k := by decide +kernel
lemma mpower0_29_r3_8_eq : ∀ k : Fin 16, mpower0_29Expr 3 8 k = mpower0_29_r3_8 k := by decide +kernel
lemma mpower0_29_r3_9_eq : ∀ k : Fin 16, mpower0_29Expr 3 9 k = mpower0_29_r3_9 k := by decide +kernel
lemma mpower0_29_r3_10_eq : ∀ k : Fin 16, mpower0_29Expr 3 10 k = mpower0_29_r3_10 k := by decide +kernel
lemma mpower0_29_r3_11_eq : ∀ k : Fin 16, mpower0_29Expr 3 11 k = mpower0_29_r3_11 k := by decide +kernel
lemma mpower0_29_r3_12_eq : ∀ k : Fin 16, mpower0_29Expr 3 12 k = mpower0_29_r3_12 k := by decide +kernel
lemma mpower0_29_r3_13_eq : ∀ k : Fin 16, mpower0_29Expr 3 13 k = mpower0_29_r3_13 k := by decide +kernel
lemma mpower0_29_r3_14_eq : ∀ k : Fin 16, mpower0_29Expr 3 14 k = mpower0_29_r3_14 k := by decide +kernel
lemma mpower0_29_r3_15_eq : ∀ k : Fin 16, mpower0_29Expr 3 15 k = mpower0_29_r3_15 k := by decide +kernel
lemma mpower0_29_r3_eq (i k : Fin 16) : mpower0_29Expr 3 i k = mpower0_29_r3 i k := by
  fin_cases i
  · exact mpower0_29_r3_0_eq k
  · exact mpower0_29_r3_1_eq k
  · exact mpower0_29_r3_2_eq k
  · exact mpower0_29_r3_3_eq k
  · exact mpower0_29_r3_4_eq k
  · exact mpower0_29_r3_5_eq k
  · exact mpower0_29_r3_6_eq k
  · exact mpower0_29_r3_7_eq k
  · exact mpower0_29_r3_8_eq k
  · exact mpower0_29_r3_9_eq k
  · exact mpower0_29_r3_10_eq k
  · exact mpower0_29_r3_11_eq k
  · exact mpower0_29_r3_12_eq k
  · exact mpower0_29_r3_13_eq k
  · exact mpower0_29_r3_14_eq k
  · exact mpower0_29_r3_15_eq k
lemma mpower0_29_r4_0_eq : ∀ k : Fin 16, mpower0_29Expr 4 0 k = mpower0_29_r4_0 k := by decide +kernel
lemma mpower0_29_r4_1_eq : ∀ k : Fin 16, mpower0_29Expr 4 1 k = mpower0_29_r4_1 k := by decide +kernel
lemma mpower0_29_r4_2_eq : ∀ k : Fin 16, mpower0_29Expr 4 2 k = mpower0_29_r4_2 k := by decide +kernel
lemma mpower0_29_r4_3_eq : ∀ k : Fin 16, mpower0_29Expr 4 3 k = mpower0_29_r4_3 k := by decide +kernel
lemma mpower0_29_r4_4_eq : ∀ k : Fin 16, mpower0_29Expr 4 4 k = mpower0_29_r4_4 k := by decide +kernel
lemma mpower0_29_r4_5_eq : ∀ k : Fin 16, mpower0_29Expr 4 5 k = mpower0_29_r4_5 k := by decide +kernel
lemma mpower0_29_r4_6_eq : ∀ k : Fin 16, mpower0_29Expr 4 6 k = mpower0_29_r4_6 k := by decide +kernel
lemma mpower0_29_r4_7_eq : ∀ k : Fin 16, mpower0_29Expr 4 7 k = mpower0_29_r4_7 k := by decide +kernel
lemma mpower0_29_r4_8_eq : ∀ k : Fin 16, mpower0_29Expr 4 8 k = mpower0_29_r4_8 k := by decide +kernel
lemma mpower0_29_r4_9_eq : ∀ k : Fin 16, mpower0_29Expr 4 9 k = mpower0_29_r4_9 k := by decide +kernel
lemma mpower0_29_r4_10_eq : ∀ k : Fin 16, mpower0_29Expr 4 10 k = mpower0_29_r4_10 k := by decide +kernel
lemma mpower0_29_r4_11_eq : ∀ k : Fin 16, mpower0_29Expr 4 11 k = mpower0_29_r4_11 k := by decide +kernel
lemma mpower0_29_r4_12_eq : ∀ k : Fin 16, mpower0_29Expr 4 12 k = mpower0_29_r4_12 k := by decide +kernel
lemma mpower0_29_r4_13_eq : ∀ k : Fin 16, mpower0_29Expr 4 13 k = mpower0_29_r4_13 k := by decide +kernel
lemma mpower0_29_r4_14_eq : ∀ k : Fin 16, mpower0_29Expr 4 14 k = mpower0_29_r4_14 k := by decide +kernel
lemma mpower0_29_r4_15_eq : ∀ k : Fin 16, mpower0_29Expr 4 15 k = mpower0_29_r4_15 k := by decide +kernel
lemma mpower0_29_r4_eq (i k : Fin 16) : mpower0_29Expr 4 i k = mpower0_29_r4 i k := by
  fin_cases i
  · exact mpower0_29_r4_0_eq k
  · exact mpower0_29_r4_1_eq k
  · exact mpower0_29_r4_2_eq k
  · exact mpower0_29_r4_3_eq k
  · exact mpower0_29_r4_4_eq k
  · exact mpower0_29_r4_5_eq k
  · exact mpower0_29_r4_6_eq k
  · exact mpower0_29_r4_7_eq k
  · exact mpower0_29_r4_8_eq k
  · exact mpower0_29_r4_9_eq k
  · exact mpower0_29_r4_10_eq k
  · exact mpower0_29_r4_11_eq k
  · exact mpower0_29_r4_12_eq k
  · exact mpower0_29_r4_13_eq k
  · exact mpower0_29_r4_14_eq k
  · exact mpower0_29_r4_15_eq k
lemma mpower0_29_r5_0_eq : ∀ k : Fin 16, mpower0_29Expr 5 0 k = mpower0_29_r5_0 k := by decide +kernel
lemma mpower0_29_r5_1_eq : ∀ k : Fin 16, mpower0_29Expr 5 1 k = mpower0_29_r5_1 k := by decide +kernel
lemma mpower0_29_r5_2_eq : ∀ k : Fin 16, mpower0_29Expr 5 2 k = mpower0_29_r5_2 k := by decide +kernel
lemma mpower0_29_r5_3_eq : ∀ k : Fin 16, mpower0_29Expr 5 3 k = mpower0_29_r5_3 k := by decide +kernel
lemma mpower0_29_r5_4_eq : ∀ k : Fin 16, mpower0_29Expr 5 4 k = mpower0_29_r5_4 k := by decide +kernel
lemma mpower0_29_r5_5_eq : ∀ k : Fin 16, mpower0_29Expr 5 5 k = mpower0_29_r5_5 k := by decide +kernel
lemma mpower0_29_r5_6_eq : ∀ k : Fin 16, mpower0_29Expr 5 6 k = mpower0_29_r5_6 k := by decide +kernel
lemma mpower0_29_r5_7_eq : ∀ k : Fin 16, mpower0_29Expr 5 7 k = mpower0_29_r5_7 k := by decide +kernel
lemma mpower0_29_r5_8_eq : ∀ k : Fin 16, mpower0_29Expr 5 8 k = mpower0_29_r5_8 k := by decide +kernel
lemma mpower0_29_r5_9_eq : ∀ k : Fin 16, mpower0_29Expr 5 9 k = mpower0_29_r5_9 k := by decide +kernel
lemma mpower0_29_r5_10_eq : ∀ k : Fin 16, mpower0_29Expr 5 10 k = mpower0_29_r5_10 k := by decide +kernel
lemma mpower0_29_r5_11_eq : ∀ k : Fin 16, mpower0_29Expr 5 11 k = mpower0_29_r5_11 k := by decide +kernel
lemma mpower0_29_r5_12_eq : ∀ k : Fin 16, mpower0_29Expr 5 12 k = mpower0_29_r5_12 k := by decide +kernel
lemma mpower0_29_r5_13_eq : ∀ k : Fin 16, mpower0_29Expr 5 13 k = mpower0_29_r5_13 k := by decide +kernel
lemma mpower0_29_r5_14_eq : ∀ k : Fin 16, mpower0_29Expr 5 14 k = mpower0_29_r5_14 k := by decide +kernel
lemma mpower0_29_r5_15_eq : ∀ k : Fin 16, mpower0_29Expr 5 15 k = mpower0_29_r5_15 k := by decide +kernel
lemma mpower0_29_r5_eq (i k : Fin 16) : mpower0_29Expr 5 i k = mpower0_29_r5 i k := by
  fin_cases i
  · exact mpower0_29_r5_0_eq k
  · exact mpower0_29_r5_1_eq k
  · exact mpower0_29_r5_2_eq k
  · exact mpower0_29_r5_3_eq k
  · exact mpower0_29_r5_4_eq k
  · exact mpower0_29_r5_5_eq k
  · exact mpower0_29_r5_6_eq k
  · exact mpower0_29_r5_7_eq k
  · exact mpower0_29_r5_8_eq k
  · exact mpower0_29_r5_9_eq k
  · exact mpower0_29_r5_10_eq k
  · exact mpower0_29_r5_11_eq k
  · exact mpower0_29_r5_12_eq k
  · exact mpower0_29_r5_13_eq k
  · exact mpower0_29_r5_14_eq k
  · exact mpower0_29_r5_15_eq k
lemma mpower0_29_eq (j : Fin 6) (i k : Fin 16) : mpower0_29Expr j i k = mpower0_29 j i k := by
  fin_cases j
  · exact mpower0_29_r0_eq i k
  · exact mpower0_29_r1_eq i k
  · exact mpower0_29_r2_eq i k
  · exact mpower0_29_r3_eq i k
  · exact mpower0_29_r4_eq i k
  · exact mpower0_29_r5_eq i k
lemma mpower0_29_contains (j : Fin 6) (i k : Fin 16) :
    (mpower0_29 j i k).Contains (momentPower 29 ((quadraturePoint j.val (16*i.val+k.val)))) := by
  rw [← mpower0_29_eq]
  exact momentPower_step_contains (mpower0_28_contains j i k) (momentPower_direct_step_contains j i k)
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders1
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
lemma hk1_0_29_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (hk1_0_29 j i k).Contains (fullFactor false 1 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power1 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 29 (power1_contains_g j i k) (mpower0_29_contains j i k)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hk1_0_29_contains_g_oai := @OAI.SharpPlanar.CachedData.hk1_0_29_contains_g_oai
