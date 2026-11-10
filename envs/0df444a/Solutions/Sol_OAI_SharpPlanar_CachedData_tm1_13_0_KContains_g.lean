-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tm1_13_0.KContains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:12:56.262675+00:00
-- url     : https://prove2.me/submissions/adb8c0cd-0568-4342-83b5-1541d666c30f

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G383
import Definitions.Def_OAIQ098G411
import Definitions.Def_OAIQ098G1533
import Definitions.Def_OAIQ098G1550
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
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel13_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tm1_13_0_sums_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
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
lemma transformed_factor_zero_contains {a : CBox} {t : ℝ} {m : ℕ}
    (ha : a.Contains (lambda t*Complex.exp (Complex.I*Real.pi*z t*m))) :
    a.Contains (complexTransformedFactor m 1 0 t) := by
  simpa only [complexTransformedFactor,complexZ_ofReal_g,complexLambda_ofReal_g,pow_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,mul_one,Complex.ofReal_natCast] using ha
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
lemma atomKernel13_0_eq (j : Fin 7) : atomKernel13_0 j = kernel0Box (atomPoints j) 13 := by
  fin_cases j <;> decide +kernel
lemma atomKernel13_0_contains (j : Fin 7) : (atomKernel13_0 j).Contains
    (complexTransformedFactor 13 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel13_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=13) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Certified quadrature and atomic bounds for the Gaussian moments -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
open scoped BigOperators

lemma tableMoment_error (a : Bool) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (ell : ℕ) :
    ‖tableMomentIntegral a m ell-tableMomentRule a m ell‖ < 1/10^22 :=
  transformedMoment_rule_error_g _ _ (table_range_mass_g a) hm0 hm1 (by norm_num) ell

lemma table_kernel_zero_contains {box : CBox} {t : ℝ} {m : ℕ}
    (ha : box.Contains ((lambda t * Complex.exp (Complex.I*Real.pi*z t*m))*1)) :
    box.Contains (complexTransformedFactor m 1 0 t) := by
  exact transformed_factor_zero_contains (by simpa only [mul_one] using ha)
lemma table_kernel_one_contains {box : CBox} {t : ℝ} {m : ℕ}
    (ha : box.Contains ((lambda t * Complex.exp (Complex.I*Real.pi*z t*m))*(Complex.I*Real.pi*z t))) :
    box.Contains (complexTransformedFactor m 1 1 t) := by
  simpa only [complexTransformedFactor,complexZ_ofReal_g,complexLambda_ofReal_g,pow_one,
    Nat.factorial_one,Nat.cast_one,div_one,Complex.ofReal_one,mul_one,Complex.ofReal_natCast] using ha

lemma tableAtomBox_contains (a : Bool) {kernel : Fin 7 → CBox} {m : ℝ} {ell : ℕ}
    (hk : ∀ j, (kernel j).Contains (complexTransformedFactor m 1 ell ((j.val:ℝ)/6))) :
    (tableAtomBox a kernel).Contains (tableMomentAtom a m ell) := by
  have hh := finSum_contains (fun j : Fin 7 => CBox.contains_mul_g
    (CBox.contains_scale_g (coefficientBox_contains_g j.val) (if j.val=0 then 1 else 2) 1 (by norm_num)) (hk j))
  have hs := CBox.contains_scale_g hh (if a then 17 else -13) 1000 (by norm_num)
  change (tableAtomBox a kernel).Contains _ at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  cases a <;> simp [tableMomentAtom,tableConstant]


lemma tableMomentK_contains {a : Bool} {m : ℝ} {ell : ℕ} {ab rb : CBox}
    (ha : ab.Contains (tableMomentAtom a m ell))
    (hr : rb.Contains (tableMomentRule a m ell)) (hm0 : 0 ≤ m) (hm1 : m ≤ 100) :
    (inflate (ab.add rb).re).Contains (tableMomentK a m ell) := by
  apply inflate_contains_g (CBox.contains_add_g ha hr).1
  unfold tableMomentK
  have he := (Complex.abs_re_le_norm (tableMomentIntegral a m ell-tableMomentRule a m ell)).trans_lt
    (tableMoment_error a hm0 hm1 ell)
  simpa only [Complex.add_re,Complex.sub_re,add_sub_add_left_eq_sub] using he
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableRuleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval bounds for the transformed Gaussian quadrature rule -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma tableRule_contains_bridge (a : Bool) (m : ℕ) (b : Bool)
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox}
    (hc : ∀ j i v, (c j i v).Contains ((fejerWeight (16*i.val+v.val):ℂ)*
      tableDensity a j.val (quadraturePoint j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains
      (lambda (quadraturePoint j.val (16*i.val+v.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+v.val))*m)*
      (if b then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+v.val)) else 1))) :
    (cachedMomentRuleBox c k).Contains (tableMomentRule a m (if b then 1 else 0)) := by
  apply cached_density_rule_contains_g hc
  intro j i v
  cases b
  · exact table_kernel_zero_contains (hk j i v)
  · exact table_kernel_one_contains (hk j i v)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments13
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

namespace tm1_13_0
lemma checked : cachedMomentRuleBox density1 kernel13_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq_g]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 13 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using @tableRule_contains_bridge true 13 false density1 kernel13_0
    density1_contains_g kernel13_0_contains_g
lemma atomChecked : tableAtomBox true atomKernel13_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 13 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel13_0_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains_g_oai : realAnswer.Contains (tableMomentK true 13 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_13_0

end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tm1_13_0.KContains_g_oai := @OAI.SharpPlanar.CachedData.tm1_13_0.KContains_g_oai
