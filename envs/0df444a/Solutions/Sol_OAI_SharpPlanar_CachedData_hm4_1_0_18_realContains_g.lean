-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm4_1_0_18.realContains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T00:27:11.18871+00:00
-- url     : https://prove2.me/submissions/3742c202-aa8c-4767-a0ce-9935664fd248

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G383
import Definitions.Def_OAIQ098G390
import Definitions.Def_OAIQ098G1238
import Definitions.Def_OAIQ098G1296
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1693
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_ha4_0_11_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hk4_0_18_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm4_1_0_18_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
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
-- module Solutions.OAIQ098_PP.PlanarPacking_HighRuleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian moment bounds at the quadrature nodes and atoms -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders4
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
lemma ha4_0_12_eq (j : Fin 7) : ha4_0_12 j = ((ha4_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha4_0_12_contains (j : Fin 7) : (ha4_0_12 j).Contains (fullFactor false 4 12 ((j.val:ℝ)/6)) := by
  rw [ha4_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_11 j) false 4 11 j (ha4_0_11_contains_g j)
lemma ha4_0_13_eq (j : Fin 7) : ha4_0_13 j = ((ha4_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha4_0_13_contains (j : Fin 7) : (ha4_0_13 j).Contains (fullFactor false 4 13 ((j.val:ℝ)/6)) := by
  rw [ha4_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_12 j) false 4 12 j (ha4_0_12_contains j)
lemma ha4_0_14_eq (j : Fin 7) : ha4_0_14 j = ((ha4_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha4_0_14_contains (j : Fin 7) : (ha4_0_14 j).Contains (fullFactor false 4 14 ((j.val:ℝ)/6)) := by
  rw [ha4_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_13 j) false 4 13 j (ha4_0_13_contains j)
lemma ha4_0_15_eq (j : Fin 7) : ha4_0_15 j = ((ha4_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha4_0_15_contains (j : Fin 7) : (ha4_0_15 j).Contains (fullFactor false 4 15 ((j.val:ℝ)/6)) := by
  rw [ha4_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_14 j) false 4 14 j (ha4_0_14_contains j)
lemma ha4_0_16_eq (j : Fin 7) : ha4_0_16 j = ((ha4_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha4_0_16_contains (j : Fin 7) : (ha4_0_16 j).Contains (fullFactor false 4 16 ((j.val:ℝ)/6)) := by
  rw [ha4_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_15 j) false 4 15 j (ha4_0_15_contains j)
lemma ha4_0_17_eq (j : Fin 7) : ha4_0_17 j = ((ha4_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha4_0_17_contains (j : Fin 7) : (ha4_0_17 j).Contains (fullFactor false 4 17 ((j.val:ℝ)/6)) := by
  rw [ha4_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_16 j) false 4 16 j (ha4_0_16_contains j)
lemma ha4_0_18_eq (j : Fin 7) : ha4_0_18 j = ((ha4_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha4_0_18_contains (j : Fin 7) : (ha4_0_18 j).Contains (fullFactor false 4 18 ((j.val:ℝ)/6)) := by
  rw [ha4_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_17 j) false 4 17 j (ha4_0_17_contains j)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_2
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
namespace hm4_1_0_18
lemma checked : cachedMomentRuleBox density1 hk4_0_18 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 4 18) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density1 hk4_0_18 (tableDensity true) (fullFactor false 4 18) density1_contains_g hk4_0_18_contains_g
lemma atomChecked : tableAtomBox true ha4_0_18 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 4 18) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha4_0_18 4 18 ha4_0_18_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains_g_oai : realAnswer.Contains (fullMoment true false 4 18) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm4_1_0_18
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm4_1_0_18.realContains_g_oai := @OAI.SharpPlanar.CachedData.hm4_1_0_18.realContains_g_oai
