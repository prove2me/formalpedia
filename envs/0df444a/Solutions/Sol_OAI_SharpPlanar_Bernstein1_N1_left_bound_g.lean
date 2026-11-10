-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein1.N1_left.bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:44:47.169206+00:00
-- url     : https://prove2.me/submissions/e45c4690-5695-45fd-8ee9-d70204f1e659

import Mathlib
import Definitions.Def_OAIQ098G061
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G400
import Definitions.Def_OAIQ098G411
import Definitions.Def_OAIQ098G960
import Definitions.Def_OAIQ098G967
import Definitions.Def_OAIQ098G975
import Definitions.Def_OAIQ098G1653
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1693
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t10_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t11_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t12_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t13_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t14_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t15_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t16_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t17_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t18_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t19_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t20_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t21_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t22_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t23_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t24_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t25_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t26_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t27_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t28_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t2_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t4_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t5_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t6_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t7_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t8_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein1_N1_left_t9_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm1_0_1_5_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm1_1_0_5_realContains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel1_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_trans1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_RBox_lower_lt_g
import Theorems.Thm_OAI_SharpPlanar_bernsteinBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
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

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma kernel0Box_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {m : ℕ}
    (hm : m < 128) : (kernel0Box p m).Contains
      (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) := by
  have he := CBox.contains_powFast_g hp.2.2.2.2 9 (4*m) (by omega)
  rw [← Complex.exp_nat_mul] at he
  have hz := CBox.contains_mul_g hp.2.1 he
  unfold kernel0Box
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  rw [pointLambda_eq_g,pointZ_eq_g]
  congr 2
  push_cast
  ring

end SharpPlanar.IntegerBasis

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

lemma transformed_factor_zero_contains {a : CBox} {t : ℝ} {m : ℕ}
    (ha : a.Contains (lambda t*Complex.exp (Complex.I*Real.pi*z t*m))) :
    a.Contains (complexTransformedFactor m 1 0 t) := by
  simpa only [complexTransformedFactor,complexZ_ofReal_g,complexLambda_ofReal_g,pow_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,mul_one,Complex.ofReal_natCast] using ha
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
lemma atomKernel1_0_eq (j : Fin 7) : atomKernel1_0 j = kernel0Box (atomPoints j) 1 := by
  fin_cases j <;> decide +kernel
lemma atomKernel1_0_contains (j : Fin 7) : (atomKernel1_0 j).Contains
    (complexTransformedFactor 1 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel1_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=1) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
lemma kernel1_0_contains (j : Fin 6) (i k : Fin 16) :
    (kernel1_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(1:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel1_0_eq_g]
  unfold kernel1_0Expr
  have hl := (gridRows_contains_g j i k).2.1
  rw [pointLambda_eq_g] at hl
  have hh := CBox.contains_mul_g hl (trans1_contains_g j i k)
  simpa only [Bool.false_eq_true,ite_false, if_false,mul_one] using hh
end SharpPlanar.CachedData

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
lemma ha1_1_0_eq (j : Fin 7) : ha1_1_0 j = atomKernel1_0 j := by fin_cases j <;> decide +kernel
lemma ha1_1_0_contains (j : Fin 7) : (ha1_1_0 j).Contains (fullFactor true 1 0 ((j.val:ℝ)/6)) := by
  rw [ha1_1_0_eq]
  simpa only [fullFactor,ite_true, if_true] using atomKernel1_0_contains j
lemma ha1_1_1_eq (j : Fin 7) : ha1_1_1 j = ((ha1_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha1_1_1_contains (j : Fin 7) : (ha1_1_1 j).Contains (fullFactor true 1 1 ((j.val:ℝ)/6)) := by
  rw [ha1_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_0 j) true 1 0 j (ha1_1_0_contains j)
lemma ha1_1_2_eq (j : Fin 7) : ha1_1_2 j = ((ha1_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha1_1_2_contains (j : Fin 7) : (ha1_1_2 j).Contains (fullFactor true 1 2 ((j.val:ℝ)/6)) := by
  rw [ha1_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_1 j) true 1 1 j (ha1_1_1_contains j)
lemma ha1_1_3_eq (j : Fin 7) : ha1_1_3 j = ((ha1_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha1_1_3_contains (j : Fin 7) : (ha1_1_3 j).Contains (fullFactor true 1 3 ((j.val:ℝ)/6)) := by
  rw [ha1_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_2 j) true 1 2 j (ha1_1_2_contains j)
lemma ha1_1_4_eq (j : Fin 7) : ha1_1_4 j = ((ha1_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha1_1_4_contains (j : Fin 7) : (ha1_1_4 j).Contains (fullFactor true 1 4 ((j.val:ℝ)/6)) := by
  rw [ha1_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_3 j) true 1 3 j (ha1_1_3_contains j)
lemma hk1_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk1_1_5 j i k).Contains (fullFactor true 1 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk1_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel1_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 1 5 (kernel1_0_contains j i k) (mpower1_5_contains_g j i k)
lemma ha1_1_5_eq (j : Fin 7) : ha1_1_5 j = ((ha1_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha1_1_5_contains (j : Fin 7) : (ha1_1_5 j).Contains (fullFactor true 1 5 ((j.val:ℝ)/6)) := by
  rw [ha1_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha1_1_4 j) true 1 4 j (ha1_1_4_contains j)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_4
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
namespace hm1_0_1_5
lemma checked : cachedMomentRuleBox density0 hk1_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 1 5) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk1_1_5 (tableDensity false) (fullFactor true 1 5) density0_contains_g hk1_1_5_contains
lemma atomChecked : tableAtomBox false ha1_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 1 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha1_1_5 1 5 ha1_1_5_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 1 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm1_0_1_5
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein1
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

namespace SharpPlanar.Bernstein1
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_left
lemma t3_checked : ((hm1_1_0_5.realAnswer).add hm1_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
lemma t3_contains : t3.Contains (sourcePower true 1 (-1/2) 2 3) := by
  rw [← t3_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm1_1_0_5.realContains_g hm1_0_1_5.realContains) (-1) 8 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 1 (-1/2) 2 r.val) := by
  fin_cases r
  · exact t0_contains_g
  · exact t1_contains_g
  · exact t2_contains_g
  · exact t3_contains
  · exact t4_contains_g
  · exact t5_contains_g
  · exact t6_contains_g
  · exact t7_contains_g
  · exact t8_contains_g
  · exact t9_contains_g
  · exact t10_contains_g
  · exact t11_contains_g
  · exact t12_contains_g
  · exact t13_contains_g
  · exact t14_contains_g
  · exact t15_contains_g
  · exact t16_contains_g
  · exact t17_contains_g
  · exact t18_contains_g
  · exact t19_contains_g
  · exact t20_contains_g
  · exact t21_contains_g
  · exact t22_contains_g
  · exact t23_contains_g
  · exact t24_contains_g
  · exact t25_contains_g
  · exact t26_contains_g
  · exact t27_contains_g
  · exact t28_contains_g
lemma bound0 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 0 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 1 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 2 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 3 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 4 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 5 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 6 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 7 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 8 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 9 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 10 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 11 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 12 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 13 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 14 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 15 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 16 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 17 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 18 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 19 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 20 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 21 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 22 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 23 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 24 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 25 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 26 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 27 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) 28 := by
  simpa only [Int.cast_ofNat] using RBox.lower_lt_g (u := 9) (v := 50) (bernsteinBox_contains_g ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound_g_oai (k : Fin 29) : (9:ℝ)/50<powerToBernstein 28 (sourcePower true 1 (-1/2) 2) k.val := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
end N1_left
end SharpPlanar.Bernstein1

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein1.N1_left.bound_g_oai := @OAI.SharpPlanar.Bernstein1.N1_left.bound_g_oai
