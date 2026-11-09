-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein28.N1_left.t7_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T02:24:23.389626+00:00
-- url     : https://prove2.me/submissions/e95d6339-a7dd-4987-90cd-5fe710317cf3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G411
import Definitions.Def_OAIQ098G1108
import Definitions.Def_OAIQ098G1116
import Definitions.Def_OAIQ098G1118
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
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm28_0_1_9_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm28_1_0_9_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel28_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_9_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powBin_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
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
lemma atomKernel28_0_eq (j : Fin 7) : atomKernel28_0 j = kernel0Box (atomPoints j) 28 := by
  fin_cases j <;> decide +kernel
lemma atomKernel28_0_contains (j : Fin 7) : (atomKernel28_0 j).Contains
    (complexTransformedFactor 28 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel28_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=28) (by decide)
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
lemma ha28_0_0_eq (j : Fin 7) : ha28_0_0 j = ((atomPoints j).direct.powBin 7 28).conj := by fin_cases j <;> decide +kernel
lemma ha28_0_0_contains (j : Fin 7) : (ha28_0_0 j).Contains (fullFactor false 28 0 ((j.val:ℝ)/6)) := by
  rw [ha28_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 28) ((j.val:ℝ)/6) 28 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 28 (by norm_num))
lemma ha28_0_1_eq (j : Fin 7) : ha28_0_1 j = ((ha28_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha28_0_1_contains (j : Fin 7) : (ha28_0_1 j).Contains (fullFactor false 28 1 ((j.val:ℝ)/6)) := by
  rw [ha28_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_0 j) false 28 0 j (ha28_0_0_contains j)
lemma ha28_0_2_eq (j : Fin 7) : ha28_0_2 j = ((ha28_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha28_0_2_contains (j : Fin 7) : (ha28_0_2 j).Contains (fullFactor false 28 2 ((j.val:ℝ)/6)) := by
  rw [ha28_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_1 j) false 28 1 j (ha28_0_1_contains j)
lemma ha28_0_3_eq (j : Fin 7) : ha28_0_3 j = ((ha28_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha28_0_3_contains (j : Fin 7) : (ha28_0_3 j).Contains (fullFactor false 28 3 ((j.val:ℝ)/6)) := by
  rw [ha28_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_2 j) false 28 2 j (ha28_0_2_contains j)
lemma ha28_0_4_eq (j : Fin 7) : ha28_0_4 j = ((ha28_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha28_0_4_contains (j : Fin 7) : (ha28_0_4 j).Contains (fullFactor false 28 4 ((j.val:ℝ)/6)) := by
  rw [ha28_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_3 j) false 28 3 j (ha28_0_3_contains j)
lemma ha28_0_5_eq (j : Fin 7) : ha28_0_5 j = ((ha28_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha28_0_5_contains (j : Fin 7) : (ha28_0_5 j).Contains (fullFactor false 28 5 ((j.val:ℝ)/6)) := by
  rw [ha28_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_4 j) false 28 4 j (ha28_0_4_contains j)
lemma ha28_0_6_eq (j : Fin 7) : ha28_0_6 j = ((ha28_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha28_0_6_contains (j : Fin 7) : (ha28_0_6 j).Contains (fullFactor false 28 6 ((j.val:ℝ)/6)) := by
  rw [ha28_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_5 j) false 28 5 j (ha28_0_5_contains j)
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
lemma ha28_1_0_eq (j : Fin 7) : ha28_1_0 j = atomKernel28_0 j := by fin_cases j <;> decide +kernel
lemma ha28_1_0_contains (j : Fin 7) : (ha28_1_0 j).Contains (fullFactor true 28 0 ((j.val:ℝ)/6)) := by
  rw [ha28_1_0_eq]
  simpa only [fullFactor,ite_true, if_true] using atomKernel28_0_contains j
lemma ha28_1_1_eq (j : Fin 7) : ha28_1_1 j = ((ha28_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha28_1_1_contains (j : Fin 7) : (ha28_1_1 j).Contains (fullFactor true 28 1 ((j.val:ℝ)/6)) := by
  rw [ha28_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_0 j) true 28 0 j (ha28_1_0_contains j)
lemma ha28_1_2_eq (j : Fin 7) : ha28_1_2 j = ((ha28_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha28_1_2_contains (j : Fin 7) : (ha28_1_2 j).Contains (fullFactor true 28 2 ((j.val:ℝ)/6)) := by
  rw [ha28_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_1 j) true 28 1 j (ha28_1_1_contains j)
lemma ha28_1_3_eq (j : Fin 7) : ha28_1_3 j = ((ha28_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha28_1_3_contains (j : Fin 7) : (ha28_1_3 j).Contains (fullFactor true 28 3 ((j.val:ℝ)/6)) := by
  rw [ha28_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_2 j) true 28 2 j (ha28_1_2_contains j)
lemma ha28_1_4_eq (j : Fin 7) : ha28_1_4 j = ((ha28_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha28_1_4_contains (j : Fin 7) : (ha28_1_4 j).Contains (fullFactor true 28 4 ((j.val:ℝ)/6)) := by
  rw [ha28_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_3 j) true 28 3 j (ha28_1_3_contains j)
lemma ha28_1_5_eq (j : Fin 7) : ha28_1_5 j = ((ha28_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha28_1_5_contains (j : Fin 7) : (ha28_1_5 j).Contains (fullFactor true 28 5 ((j.val:ℝ)/6)) := by
  rw [ha28_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_4 j) true 28 4 j (ha28_1_4_contains j)
lemma ha28_1_6_eq (j : Fin 7) : ha28_1_6 j = ((ha28_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha28_1_6_contains (j : Fin 7) : (ha28_1_6 j).Contains (fullFactor true 28 6 ((j.val:ℝ)/6)) := by
  rw [ha28_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_5 j) true 28 5 j (ha28_1_5_contains j)
lemma ha28_1_7_eq (j : Fin 7) : ha28_1_7 j = ((ha28_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha28_1_7_contains (j : Fin 7) : (ha28_1_7 j).Contains (fullFactor true 28 7 ((j.val:ℝ)/6)) := by
  rw [ha28_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_6 j) true 28 6 j (ha28_1_6_contains j)
lemma ha28_1_8_eq (j : Fin 7) : ha28_1_8 j = ((ha28_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha28_1_8_contains (j : Fin 7) : (ha28_1_8 j).Contains (fullFactor true 28 8 ((j.val:ℝ)/6)) := by
  rw [ha28_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_7 j) true 28 7 j (ha28_1_7_contains j)
lemma hk28_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_9 j i k).Contains (fullFactor true 28 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 9 (kernel28_0_contains_g j i k) (mpower1_9_contains_g j i k)
lemma ha28_1_9_eq (j : Fin 7) : ha28_1_9 j = ((ha28_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha28_1_9_contains (j : Fin 7) : (ha28_1_9 j).Contains (fullFactor true 28 9 ((j.val:ℝ)/6)) := by
  rw [ha28_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_8 j) true 28 8 j (ha28_1_8_contains j)
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
namespace hm28_1_0_9
lemma atomChecked : tableAtomBox true ha28_0_9 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 28 9) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha28_0_9 28 9 ha28_0_9_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 28 9) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains_g (by norm_num) (by norm_num)
end hm28_1_0_9
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_11
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
namespace hm28_0_1_9
lemma checked : cachedMomentRuleBox density0 hk28_1_9 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 28 9) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk28_1_9 (tableDensity false) (fullFactor true 28 9) density0_contains_g hk28_1_9_contains
lemma atomChecked : tableAtomBox false ha28_1_9 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 28 9) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha28_1_9 28 9 ha28_1_9_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 28 9) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm28_0_1_9
end SharpPlanar.CachedData

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
lemma t7_checked : ((hm28_1_0_9.realAnswer).add hm28_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
lemma t7_contains_g_oai : t7.Contains (sourcePower true 28 (-1/2) 2 7) := by
  rw [← t7_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm28_1_0_9.realContains hm28_0_1_9.realContains) (-1) 128 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
end N1_left
end SharpPlanar.Bernstein28

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein28.N1_left.t7_contains_g_oai := @OAI.SharpPlanar.Bernstein28.N1_left.t7_contains_g_oai
