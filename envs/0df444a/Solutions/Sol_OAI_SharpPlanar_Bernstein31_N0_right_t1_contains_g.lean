-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein31.N0_right.t1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T08:33:33.723658+00:00
-- url     : https://prove2.me/submissions/f2328e9b-38ba-450e-9f54-38f35cd4bd84

import Mathlib
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G319
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G628
import Definitions.Def_OAIQ098G1118
import Definitions.Def_OAIQ098G1143
import Definitions.Def_OAIQ098G1464
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1693
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm31_0_0_3_checked_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm31_1_1_3_realContains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power30_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powBin_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_directMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma zeroBox_contains : zeroBox.Contains 0 := by simp [zeroBox,CBox.Contains,RBox.Contains]
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

lemma finSum_contains {N : ℕ} {f : Fin N → CBox} {g : Fin N → ℂ}
    (h : ∀ i, (f i).Contains (g i)) : (finSum f).Contains (∑ i, g i) := by
  induction N with
  | zero => simpa [finSum] using zeroBox_contains
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    exact CBox.contains_add_g (h 0) (ih (fun i => h i.succ))

end SharpPlanar.IntegerIntervals

end OAI
end

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
lemma direct_factor_step (m : ℝ) (ell : ℕ) (t : ℂ) :
    complexDirectFactor m 1 (ell+1) t = complexDirectFactor m 1 ell t *
      (Complex.I*Real.pi*t) / ((ell+1:ℕ):ℂ) := by
  unfold complexDirectFactor
  simp only [Complex.ofReal_one,mul_one,pow_succ,Nat.factorial_succ,Nat.cast_mul]
  ring
lemma transformed_factor_step (m : ℝ) (ell : ℕ) (t : ℂ) :
    complexTransformedFactor m 1 (ell+1) t = complexTransformedFactor m 1 ell t *
      (Complex.I*Real.pi*complexZ t) / ((ell+1:ℕ):ℂ) := by
  unfold complexTransformedFactor
  simp only [Complex.ofReal_one,mul_one,pow_succ,Nat.factorial_succ,Nat.cast_mul]
  ring

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_AtomKernels
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
lemma atomPoints_contains (j : Fin 7) : (atomPoints j).Contains ((j.val:ℝ)/6) := by
  fin_cases j
  · simpa [atomPoints] using atomPoint0_contains_g
  · simpa [atomPoints] using atomPoint1_contains_g
  · simpa [atomPoints] using atomPoint2_contains_g
  · simpa [atomPoints] using atomPoint3_contains_g
  · simpa [atomPoints] using atomPoint4_contains_g
  · simpa [atomPoints] using atomPoint5_contains_g
  · simpa [atomPoints] using atomPoint6_contains_g
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
lemma fullAtomBox_contains (a tr : Bool) {kernel : Fin 7 → CBox} {m : ℝ} {ell : ℕ}
    (hk : ∀ j, (kernel j).Contains (fullFactor tr m ell ((j.val:ℝ)/6))) :
    (tableAtomBox a kernel).Contains (fullMomentAtom a tr m ell) := by
  have hh := finSum_contains (fun j : Fin 7 => CBox.contains_mul_g
    (CBox.contains_scale_g (coefficientBox_contains_g j.val) (if j.val=0 then 1 else 2) 1 (by norm_num)) (hk j))
  have hs := CBox.contains_scale_g hh (if a then 17 else -13) 1000 (by norm_num)
  change (tableAtomBox a kernel).Contains _ at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  cases a <;> simp [fullMomentAtom,tableConstant]
lemma fullMoment_contains {a tr : Bool} {m : ℝ} {ell : ℕ} {ab rb : CBox}
    (ha : ab.Contains (fullMomentAtom a tr m ell))
    (hr : rb.Contains (fullMomentRule a tr m ell)) (hm0 : 0 ≤ m) (hm1 : m ≤ 100) :
    (inflate (ab.add rb).re).Contains (fullMoment a tr m ell) := by
  apply inflate_contains_g (CBox.contains_add_g ha hr).1
  unfold fullMoment
  have he := (Complex.abs_re_le_norm (fullMomentIntegral a tr m ell-fullMomentRule a tr m ell)).trans_lt
    (fullMoment_error a tr hm0 hm1 ell)
  simpa only [Complex.add_re,Complex.sub_re,add_sub_add_left_eq_sub] using he
lemma fullFactor_step_contains {a b : CBox} {tr : Bool} {m : ℝ} {ell : ℕ} {t : ℝ}
    (ha : a.Contains (fullFactor tr m ell t))
    (hb : b.Contains (Complex.I*Real.pi*(if tr then z t else (t:ℂ)))) :
    ((a.mul b).scale 1 (ell+1)).Contains (fullFactor tr m (ell+1) t) := by
  cases tr
  · change a.Contains (complexDirectFactor m 1 ell t) at ha
    change b.Contains (Complex.I*Real.pi*t) at hb
    change ((a.mul b).scale 1 (ell+1)).Contains (complexDirectFactor m 1 (ell+1) t)
    rw [direct_factor_step]
    exact factor_step_contains ha hb ell
  · change a.Contains (complexTransformedFactor m 1 ell t) at ha
    change b.Contains (Complex.I*Real.pi*z t) at hb
    change ((a.mul b).scale 1 (ell+1)).Contains (complexTransformedFactor m 1 (ell+1) t)
    rw [transformed_factor_step,complexZ_ofReal_g]
    exact factor_step_contains ha hb ell
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
lemma power31_r0_0_eq : ∀ k : Fin 16, power31Expr 0 0 k = power31_r0_0 k := by decide +kernel
lemma power31_r0_1_eq : ∀ k : Fin 16, power31Expr 0 1 k = power31_r0_1 k := by decide +kernel
lemma power31_r0_2_eq : ∀ k : Fin 16, power31Expr 0 2 k = power31_r0_2 k := by decide +kernel
lemma power31_r0_3_eq : ∀ k : Fin 16, power31Expr 0 3 k = power31_r0_3 k := by decide +kernel
lemma power31_r0_4_eq : ∀ k : Fin 16, power31Expr 0 4 k = power31_r0_4 k := by decide +kernel
lemma power31_r0_5_eq : ∀ k : Fin 16, power31Expr 0 5 k = power31_r0_5 k := by decide +kernel
lemma power31_r0_6_eq : ∀ k : Fin 16, power31Expr 0 6 k = power31_r0_6 k := by decide +kernel
lemma power31_r0_7_eq : ∀ k : Fin 16, power31Expr 0 7 k = power31_r0_7 k := by decide +kernel
lemma power31_r0_8_eq : ∀ k : Fin 16, power31Expr 0 8 k = power31_r0_8 k := by decide +kernel
lemma power31_r0_9_eq : ∀ k : Fin 16, power31Expr 0 9 k = power31_r0_9 k := by decide +kernel
lemma power31_r0_10_eq : ∀ k : Fin 16, power31Expr 0 10 k = power31_r0_10 k := by decide +kernel
lemma power31_r0_11_eq : ∀ k : Fin 16, power31Expr 0 11 k = power31_r0_11 k := by decide +kernel
lemma power31_r0_12_eq : ∀ k : Fin 16, power31Expr 0 12 k = power31_r0_12 k := by decide +kernel
lemma power31_r0_13_eq : ∀ k : Fin 16, power31Expr 0 13 k = power31_r0_13 k := by decide +kernel
lemma power31_r0_14_eq : ∀ k : Fin 16, power31Expr 0 14 k = power31_r0_14 k := by decide +kernel
lemma power31_r0_15_eq : ∀ k : Fin 16, power31Expr 0 15 k = power31_r0_15 k := by decide +kernel
lemma power31_r0_eq (i k : Fin 16) : power31Expr 0 i k = power31_r0 i k := by
  fin_cases i
  · exact power31_r0_0_eq k
  · exact power31_r0_1_eq k
  · exact power31_r0_2_eq k
  · exact power31_r0_3_eq k
  · exact power31_r0_4_eq k
  · exact power31_r0_5_eq k
  · exact power31_r0_6_eq k
  · exact power31_r0_7_eq k
  · exact power31_r0_8_eq k
  · exact power31_r0_9_eq k
  · exact power31_r0_10_eq k
  · exact power31_r0_11_eq k
  · exact power31_r0_12_eq k
  · exact power31_r0_13_eq k
  · exact power31_r0_14_eq k
  · exact power31_r0_15_eq k
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
lemma power31_r2_0_eq : ∀ k : Fin 16, power31Expr 2 0 k = power31_r2_0 k := by decide +kernel
lemma power31_r2_1_eq : ∀ k : Fin 16, power31Expr 2 1 k = power31_r2_1 k := by decide +kernel
lemma power31_r2_2_eq : ∀ k : Fin 16, power31Expr 2 2 k = power31_r2_2 k := by decide +kernel
lemma power31_r2_3_eq : ∀ k : Fin 16, power31Expr 2 3 k = power31_r2_3 k := by decide +kernel
lemma power31_r2_4_eq : ∀ k : Fin 16, power31Expr 2 4 k = power31_r2_4 k := by decide +kernel
lemma power31_r2_5_eq : ∀ k : Fin 16, power31Expr 2 5 k = power31_r2_5 k := by decide +kernel
lemma power31_r2_6_eq : ∀ k : Fin 16, power31Expr 2 6 k = power31_r2_6 k := by decide +kernel
lemma power31_r2_7_eq : ∀ k : Fin 16, power31Expr 2 7 k = power31_r2_7 k := by decide +kernel
lemma power31_r2_8_eq : ∀ k : Fin 16, power31Expr 2 8 k = power31_r2_8 k := by decide +kernel
lemma power31_r2_9_eq : ∀ k : Fin 16, power31Expr 2 9 k = power31_r2_9 k := by decide +kernel
lemma power31_r2_10_eq : ∀ k : Fin 16, power31Expr 2 10 k = power31_r2_10 k := by decide +kernel
lemma power31_r2_11_eq : ∀ k : Fin 16, power31Expr 2 11 k = power31_r2_11 k := by decide +kernel
lemma power31_r2_12_eq : ∀ k : Fin 16, power31Expr 2 12 k = power31_r2_12 k := by decide +kernel
lemma power31_r2_13_eq : ∀ k : Fin 16, power31Expr 2 13 k = power31_r2_13 k := by decide +kernel
lemma power31_r2_14_eq : ∀ k : Fin 16, power31Expr 2 14 k = power31_r2_14 k := by decide +kernel
lemma power31_r2_15_eq : ∀ k : Fin 16, power31Expr 2 15 k = power31_r2_15 k := by decide +kernel
lemma power31_r2_eq (i k : Fin 16) : power31Expr 2 i k = power31_r2 i k := by
  fin_cases i
  · exact power31_r2_0_eq k
  · exact power31_r2_1_eq k
  · exact power31_r2_2_eq k
  · exact power31_r2_3_eq k
  · exact power31_r2_4_eq k
  · exact power31_r2_5_eq k
  · exact power31_r2_6_eq k
  · exact power31_r2_7_eq k
  · exact power31_r2_8_eq k
  · exact power31_r2_9_eq k
  · exact power31_r2_10_eq k
  · exact power31_r2_11_eq k
  · exact power31_r2_12_eq k
  · exact power31_r2_13_eq k
  · exact power31_r2_14_eq k
  · exact power31_r2_15_eq k
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
lemma power31_r4_0_eq : ∀ k : Fin 16, power31Expr 4 0 k = power31_r4_0 k := by decide +kernel
lemma power31_r4_1_eq : ∀ k : Fin 16, power31Expr 4 1 k = power31_r4_1 k := by decide +kernel
lemma power31_r4_2_eq : ∀ k : Fin 16, power31Expr 4 2 k = power31_r4_2 k := by decide +kernel
lemma power31_r4_3_eq : ∀ k : Fin 16, power31Expr 4 3 k = power31_r4_3 k := by decide +kernel
lemma power31_r4_4_eq : ∀ k : Fin 16, power31Expr 4 4 k = power31_r4_4 k := by decide +kernel
lemma power31_r4_5_eq : ∀ k : Fin 16, power31Expr 4 5 k = power31_r4_5 k := by decide +kernel
lemma power31_r4_6_eq : ∀ k : Fin 16, power31Expr 4 6 k = power31_r4_6 k := by decide +kernel
lemma power31_r4_7_eq : ∀ k : Fin 16, power31Expr 4 7 k = power31_r4_7 k := by decide +kernel
lemma power31_r4_8_eq : ∀ k : Fin 16, power31Expr 4 8 k = power31_r4_8 k := by decide +kernel
lemma power31_r4_9_eq : ∀ k : Fin 16, power31Expr 4 9 k = power31_r4_9 k := by decide +kernel
lemma power31_r4_10_eq : ∀ k : Fin 16, power31Expr 4 10 k = power31_r4_10 k := by decide +kernel
lemma power31_r4_11_eq : ∀ k : Fin 16, power31Expr 4 11 k = power31_r4_11 k := by decide +kernel
lemma power31_r4_12_eq : ∀ k : Fin 16, power31Expr 4 12 k = power31_r4_12 k := by decide +kernel
lemma power31_r4_13_eq : ∀ k : Fin 16, power31Expr 4 13 k = power31_r4_13 k := by decide +kernel
lemma power31_r4_14_eq : ∀ k : Fin 16, power31Expr 4 14 k = power31_r4_14 k := by decide +kernel
lemma power31_r4_15_eq : ∀ k : Fin 16, power31Expr 4 15 k = power31_r4_15 k := by decide +kernel
lemma power31_r4_eq (i k : Fin 16) : power31Expr 4 i k = power31_r4 i k := by
  fin_cases i
  · exact power31_r4_0_eq k
  · exact power31_r4_1_eq k
  · exact power31_r4_2_eq k
  · exact power31_r4_3_eq k
  · exact power31_r4_4_eq k
  · exact power31_r4_5_eq k
  · exact power31_r4_6_eq k
  · exact power31_r4_7_eq k
  · exact power31_r4_8_eq k
  · exact power31_r4_9_eq k
  · exact power31_r4_10_eq k
  · exact power31_r4_11_eq k
  · exact power31_r4_12_eq k
  · exact power31_r4_13_eq k
  · exact power31_r4_14_eq k
  · exact power31_r4_15_eq k
lemma power31_r5_0_eq : ∀ k : Fin 16, power31Expr 5 0 k = power31_r5_0 k := by decide +kernel
lemma power31_r5_1_eq : ∀ k : Fin 16, power31Expr 5 1 k = power31_r5_1 k := by decide +kernel
lemma power31_r5_2_eq : ∀ k : Fin 16, power31Expr 5 2 k = power31_r5_2 k := by decide +kernel
lemma power31_r5_3_eq : ∀ k : Fin 16, power31Expr 5 3 k = power31_r5_3 k := by decide +kernel
lemma power31_r5_4_eq : ∀ k : Fin 16, power31Expr 5 4 k = power31_r5_4 k := by decide +kernel
lemma power31_r5_5_eq : ∀ k : Fin 16, power31Expr 5 5 k = power31_r5_5 k := by decide +kernel
lemma power31_r5_6_eq : ∀ k : Fin 16, power31Expr 5 6 k = power31_r5_6 k := by decide +kernel
lemma power31_r5_7_eq : ∀ k : Fin 16, power31Expr 5 7 k = power31_r5_7 k := by decide +kernel
lemma power31_r5_8_eq : ∀ k : Fin 16, power31Expr 5 8 k = power31_r5_8 k := by decide +kernel
lemma power31_r5_9_eq : ∀ k : Fin 16, power31Expr 5 9 k = power31_r5_9 k := by decide +kernel
lemma power31_r5_10_eq : ∀ k : Fin 16, power31Expr 5 10 k = power31_r5_10 k := by decide +kernel
lemma power31_r5_11_eq : ∀ k : Fin 16, power31Expr 5 11 k = power31_r5_11 k := by decide +kernel
lemma power31_r5_12_eq : ∀ k : Fin 16, power31Expr 5 12 k = power31_r5_12 k := by decide +kernel
lemma power31_r5_13_eq : ∀ k : Fin 16, power31Expr 5 13 k = power31_r5_13 k := by decide +kernel
lemma power31_r5_14_eq : ∀ k : Fin 16, power31Expr 5 14 k = power31_r5_14 k := by decide +kernel
lemma power31_r5_15_eq : ∀ k : Fin 16, power31Expr 5 15 k = power31_r5_15 k := by decide +kernel
lemma power31_r5_eq (i k : Fin 16) : power31Expr 5 i k = power31_r5 i k := by
  fin_cases i
  · exact power31_r5_0_eq k
  · exact power31_r5_1_eq k
  · exact power31_r5_2_eq k
  · exact power31_r5_3_eq k
  · exact power31_r5_4_eq k
  · exact power31_r5_5_eq k
  · exact power31_r5_6_eq k
  · exact power31_r5_7_eq k
  · exact power31_r5_8_eq k
  · exact power31_r5_9_eq k
  · exact power31_r5_10_eq k
  · exact power31_r5_11_eq k
  · exact power31_r5_12_eq k
  · exact power31_r5_13_eq k
  · exact power31_r5_14_eq k
  · exact power31_r5_15_eq k
lemma power31_eq (j : Fin 6) (i k : Fin 16) : power31Expr j i k = power31 j i k := by
  fin_cases j
  · exact power31_r0_eq i k
  · exact power31_r1_eq i k
  · exact power31_r2_eq i k
  · exact power31_r3_eq i k
  · exact power31_r4_eq i k
  · exact power31_r5_eq i k
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
lemma direct_factor_zero_full {a : CBox} {t : ℝ} {m : ℕ}
    (ha : a.Contains (Complex.exp (-Complex.I*Real.pi*t*m))) :
    a.conj.Contains (fullFactor false m 0 t) := by
  simpa only [fullFactor,Bool.false_eq_true,ite_false, if_false] using direct_factor_zero_contains ha
lemma direct_power_bin_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {n : ℕ}
    (hn : n < 128) : (p.direct.powBin 7 n).Contains
      (Complex.exp (-Complex.I*Real.pi*t*n)) := by
  have he := CBox.contains_powBin_g hp.2.2.2.1 7 n hn
  rw [← Complex.exp_nat_mul] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring
lemma fullFactor_step_atom_contains {a : CBox} {tr : Bool} {m : ℝ} {ell : ℕ}
    (j : Fin 7) (ha : a.Contains (fullFactor tr m ell ((j.val:ℝ)/6))) :
    ((a.mul (if tr then piI.mul (CachedData.atomPoints j).z else
      piI.mul (rcast (CachedData.atomPoints j).t))).scale 1 (ell+1)).Contains
      (fullFactor tr m (ell+1) ((j.val:ℝ)/6)) := by
  have hap : a.Contains (fullFactor tr m ell (((j.val:ℝ)/6:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using ha
  have hb : (if tr then piI.mul (CachedData.atomPoints j).z else
      piI.mul (rcast (CachedData.atomPoints j).t)).Contains
      (Complex.I*Real.pi*(if tr then z ((j.val:ℝ)/6) else (((j.val:ℝ)/6:ℝ):ℂ))) := by
    cases tr
    · simpa only [Bool.false_eq_true,ite_false, if_false] using
        CBox.contains_mul_g piI_contains_g (rcast_contains_g (CachedData.atomPoints_contains j).1)
    · have hh := (CachedData.atomPoints_contains j).2.2.1
      rw [pointZ_eq_g] at hh
      simpa only [ite_true, if_true] using CBox.contains_mul_g piI_contains_g hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
    fullFactor_step_contains hap hb
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
lemma ha31_0_0_eq (j : Fin 7) : ha31_0_0 j = ((atomPoints j).direct.powBin 7 31).conj := by fin_cases j <;> decide +kernel
lemma ha31_0_0_contains (j : Fin 7) : (ha31_0_0 j).Contains (fullFactor false 31 0 ((j.val:ℝ)/6)) := by
  rw [ha31_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 31) ((j.val:ℝ)/6) 31 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 31 (by norm_num))
lemma ha31_0_1_eq (j : Fin 7) : ha31_0_1 j = ((ha31_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha31_0_1_contains (j : Fin 7) : (ha31_0_1 j).Contains (fullFactor false 31 1 ((j.val:ℝ)/6)) := by
  rw [ha31_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_0 j) false 31 0 j (ha31_0_0_contains j)
lemma ha31_0_2_eq (j : Fin 7) : ha31_0_2 j = ((ha31_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha31_0_2_contains (j : Fin 7) : (ha31_0_2 j).Contains (fullFactor false 31 2 ((j.val:ℝ)/6)) := by
  rw [ha31_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_1 j) false 31 1 j (ha31_0_1_contains j)
lemma hk31_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_3 j i k).Contains (fullFactor false 31 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 3 (power31_contains j i k) (mpower0_3_contains j i k)
lemma ha31_0_3_eq (j : Fin 7) : ha31_0_3 j = ((ha31_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha31_0_3_contains (j : Fin 7) : (ha31_0_3 j).Contains (fullFactor false 31 3 ((j.val:ℝ)/6)) := by
  rw [ha31_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_2 j) false 31 2 j (ha31_0_2_contains j)
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
namespace hm31_0_0_3
lemma contains : ans.Contains (fullMomentRule false false 31 3) := by
  rw [← checked_g]
  exact @cached_density_rule_contains_g density0 hk31_0_3 (tableDensity false) (fullFactor false 31 3) density0_contains_g hk31_0_3_contains
lemma atomChecked : tableAtomBox false ha31_0_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 31 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha31_0_3 31 3 ha31_0_3_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 31 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm31_0_0_3
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein31
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

namespace SharpPlanar.Bernstein31
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N0_right
lemma t1_checked : ((hm31_0_0_3.realAnswer).add hm31_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
lemma t1_contains_g_oai : t1.Contains (sourcePower false 31 (1/1) 2 1) := by
  rw [← t1_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm31_0_0_3.realContains hm31_1_1_3.realContains_g) (-1) 1 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
end N0_right
end SharpPlanar.Bernstein31

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein31.N0_right.t1_contains_g_oai := @OAI.SharpPlanar.Bernstein31.N0_right.t1_contains_g_oai
