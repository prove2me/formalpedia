-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein28.N1_left.t11_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:33:06.34601+00:00
-- url     : https://prove2.me/submissions/51065d05-de9a-48c3-9d16-fcfa8c43b2e6

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G383
import Definitions.Def_OAIQ098G1092
import Definitions.Def_OAIQ098G1108
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1693
import Definitions.Def_OAIQ098G1697
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_ha28_0_5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm28_1_0_13_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_13_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power27_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power28_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_RBox_contains_of_abs_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_directMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_sharp_moment_bound_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_table_coeff_mass_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_nonneg_g
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
-- module Solutions.OAIQ098_PP.PlanarPacking_FullMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma fullMoment_transformed (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a true m ell=K (tableData a) ell m/(ell.factorial:ℝ) :=
  tableMomentK_eq_g a m ell
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm bounds for the rational coefficient family

Finite rational sums give bounds for the mass of the cardinal coefficients.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
lemma table_constant_bound (a : Bool) : |(tableData a).C| ≤ (17:ℝ)/1000 := by
  cases a <;> norm_num [tableData,tableConstant]
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers30
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
lemma power28_contains (j : Fin 6) (i k : Fin 16) :
    (power28 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(28:ℕ))) := by
  rw [← power28_eq_g]
  unfold power28Expr
  convert exp_direct_step_g (power27_contains_g j i k) (gridRows_contains_g j i k).2.2.2.1 using 1
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders28
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
lemma ha28_0_6_eq (j : Fin 7) : ha28_0_6 j = ((ha28_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha28_0_6_contains (j : Fin 7) : (ha28_0_6 j).Contains (fullFactor false 28 6 ((j.val:ℝ)/6)) := by
  rw [ha28_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_5 j) false 28 5 j (ha28_0_5_contains_g j)
lemma ha28_0_7_eq (j : Fin 7) : ha28_0_7 j = ((ha28_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha28_0_7_contains (j : Fin 7) : (ha28_0_7 j).Contains (fullFactor false 28 7 ((j.val:ℝ)/6)) := by
  rw [ha28_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_6 j) false 28 6 j (ha28_0_6_contains j)
lemma ha28_0_8_eq (j : Fin 7) : ha28_0_8 j = ((ha28_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha28_0_8_contains (j : Fin 7) : (ha28_0_8 j).Contains (fullFactor false 28 8 ((j.val:ℝ)/6)) := by
  rw [ha28_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_7 j) false 28 7 j (ha28_0_7_contains j)
lemma ha28_0_9_eq (j : Fin 7) : ha28_0_9 j = ((ha28_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha28_0_9_contains (j : Fin 7) : (ha28_0_9 j).Contains (fullFactor false 28 9 ((j.val:ℝ)/6)) := by
  rw [ha28_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_8 j) false 28 8 j (ha28_0_8_contains j)
lemma ha28_0_10_eq (j : Fin 7) : ha28_0_10 j = ((ha28_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha28_0_10_contains (j : Fin 7) : (ha28_0_10 j).Contains (fullFactor false 28 10 ((j.val:ℝ)/6)) := by
  rw [ha28_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_9 j) false 28 9 j (ha28_0_9_contains j)
lemma ha28_0_11_eq (j : Fin 7) : ha28_0_11 j = ((ha28_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha28_0_11_contains (j : Fin 7) : (ha28_0_11 j).Contains (fullFactor false 28 11 ((j.val:ℝ)/6)) := by
  rw [ha28_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_10 j) false 28 10 j (ha28_0_10_contains j)
lemma ha28_0_12_eq (j : Fin 7) : ha28_0_12 j = ((ha28_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha28_0_12_contains (j : Fin 7) : (ha28_0_12 j).Contains (fullFactor false 28 12 ((j.val:ℝ)/6)) := by
  rw [ha28_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_11 j) false 28 11 j (ha28_0_11_contains j)
lemma hk28_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_13 j i k).Contains (fullFactor false 28 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 13 (power28_contains j i k) (mpower0_13_contains_g j i k)
lemma ha28_0_13_eq (j : Fin 7) : ha28_0_13 j = ((ha28_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha28_0_13_contains (j : Fin 7) : (ha28_0_13 j).Contains (fullFactor false 28 13 ((j.val:ℝ)/6)) := by
  rw [ha28_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_12 j) false 28 12 j (ha28_0_12_contains j)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_1
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
namespace hm28_1_0_13
lemma checked : cachedMomentRuleBox density1 hk28_0_13 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 28 13) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density1 hk28_0_13 (tableDensity true) (fullFactor false 28 13) density1_contains_g hk28_0_13_contains
lemma atomChecked : tableAtomBox true ha28_0_13 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 28 13) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha28_0_13 28 13 ha28_0_13_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 28 13) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm28_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MixedTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma fullMoment_transformed_bound (a : Bool) (ell n : ℕ) :
    |fullMoment a true n ell|≤transformTaylor ell n/(ell.factorial:ℝ) := by
  rw [fullMoment_transformed,abs_div,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ)≤(ell.factorial:ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hk:=sharp_moment_bound_g (tableData a) ell (Nat.cast_nonneg n)
  have hm:=table_coeff_mass_g a
  have hc:=table_constant_bound a
  have htn:=transformEnvelope_nonneg_g ell (Nat.cast_nonneg n)
  have han:=atomicEnvelope_nonneg_g ell (n:ℝ)
  have hk1:=mul_le_mul (show |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖≤(23:ℝ)/10 by linarith)
    (transformEnvelope_le_rat_g ell n) htn (by norm_num : (0:ℝ)≤23/10)
  have hk2:=mul_le_mul hc (atomicEnvelope_le_rat_g ell n) han (by norm_num : (0:ℝ)≤17/1000)
  unfold transformTaylor
  exact hk.trans (add_le_add hk1 hk2)
lemma fullMoment_transformed_cap (a : Bool) (ell n : ℕ) {B : ℝ}
    (hB : transformTaylor ell n/(ell.factorial:ℝ)≤B) :
    |fullMoment a true n ell|≤B := (fullMoment_transformed_bound a ell n).trans hB
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MixedBound28
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

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_28_13 : transformTaylor 13 28/((Nat.factorial 13):ℝ)≤(23959747803008070727398235:ℝ)/1000000000000000000000000000000 := by
  first | (simp [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein28
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

namespace SharpPlanar.Bernstein28
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_left
lemma tr11_contains : tr11.Contains (fullMoment false true 28 13) := by
  apply RBox.contains_of_abs_g (fullMoment_transformed_cap false 13 28 mixed_28_13) <;> norm_num [tr11,precision]
lemma t11_checked : ((hm28_1_0_13.realAnswer).add tr11).scale (-1) 2048=t11 := by decide +kernel
lemma t11_contains_g_oai : t11.Contains (sourcePower true 28 (-1/2) 2 11) := by
  rw [← t11_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm28_1_0_13.realContains tr11_contains) (-1) 2048 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
end N1_left
end SharpPlanar.Bernstein28

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein28.N1_left.t11_contains_g_oai := @OAI.SharpPlanar.Bernstein28.N1_left.t11_contains_g_oai
