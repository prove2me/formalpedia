-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein31.N0_left.bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:52:13.834755+00:00
-- url     : https://prove2.me/submissions/c28686c3-3c96-4114-8698-c1166b11c822

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G319
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G411
import Definitions.Def_OAIQ098G1123
import Definitions.Def_OAIQ098G1132
import Definitions.Def_OAIQ098G1134
import Definitions.Def_OAIQ098G1143
import Definitions.Def_OAIQ098G1490
import Definitions.Def_OAIQ098G1653
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1693
import Definitions.Def_OAIQ098G1697
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t10_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t11_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t2_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t3_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t5_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t7_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t8_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein31_N0_left_t9_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm31_0_0_6_realContains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel31_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower0_8_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_mpower1_6_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power30_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power31_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_exp_direct_step_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
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
import Theorems.Thm_OAI_SharpPlanar_RBox_contains_of_abs_g
import Theorems.Thm_OAI_SharpPlanar_RBox_lower_lt_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_bernsteinBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_14_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_15_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_16_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_17_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_18_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_19_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_20_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_21_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_22_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_23_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_24_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_25_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_26_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_27_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_28_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_29_g
import Theorems.Thm_OAI_SharpPlanar_coarse_31_30_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_directMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_sharp_moment_bound_g
import Theorems.Thm_OAI_SharpPlanar_sourcePower_of_cap_g
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
lemma atomKernel31_0_eq (j : Fin 7) : atomKernel31_0 j = kernel0Box (atomPoints j) 31 := by
  fin_cases j <;> decide +kernel
lemma atomKernel31_0_contains (j : Fin 7) : (atomKernel31_0 j).Contains
    (complexTransformedFactor 31 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel31_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=31) (by decide)
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
lemma momentPower_direct_contains {a b : CBox} {t : ℝ} {m ell : ℕ}
    (ha : a.Contains (Complex.exp (-Complex.I*Real.pi*t*m)))
    (hb : b.Contains (momentPower ell t)) :
    (a.conj.mul b).Contains (complexDirectFactor m 1 ell t) := by
  have hh := CBox.contains_mul_g (direct_factor_zero_contains ha) hb
  simpa only [complexDirectFactor,Complex.ofReal_one,mul_one,pow_zero,Nat.factorial_zero,
    Nat.cast_one,div_one,momentPower,mul_div_assoc] using hh
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers10
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
lemma mpower1_6_contains (j : Fin 6) (i k : Fin 16) :
    (mpower1_6 j i k).Contains (momentPower 6 (z (quadraturePoint j.val (16*i.val+k.val)))) := by
  rw [← mpower1_6_eq_g]
  exact momentPower_step_contains (mpower1_5_contains_g j i k) (momentPower_trans_step_contains j i k)
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
lemma power31_contains (j : Fin 6) (i k : Fin 16) :
    (power31 j i k).Contains (Complex.exp (-Complex.I*Real.pi*quadraturePoint j.val (16*i.val+k.val)*(31:ℕ))) := by
  rw [← power31_eq_g]
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
lemma ha31_0_3_eq (j : Fin 7) : ha31_0_3 j = ((ha31_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha31_0_3_contains (j : Fin 7) : (ha31_0_3 j).Contains (fullFactor false 31 3 ((j.val:ℝ)/6)) := by
  rw [ha31_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_2 j) false 31 2 j (ha31_0_2_contains j)
lemma ha31_0_4_eq (j : Fin 7) : ha31_0_4 j = ((ha31_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha31_0_4_contains (j : Fin 7) : (ha31_0_4 j).Contains (fullFactor false 31 4 ((j.val:ℝ)/6)) := by
  rw [ha31_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_3 j) false 31 3 j (ha31_0_3_contains j)
lemma ha31_0_5_eq (j : Fin 7) : ha31_0_5 j = ((ha31_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha31_0_5_contains (j : Fin 7) : (ha31_0_5 j).Contains (fullFactor false 31 5 ((j.val:ℝ)/6)) := by
  rw [ha31_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_4 j) false 31 4 j (ha31_0_4_contains j)
lemma ha31_0_6_eq (j : Fin 7) : ha31_0_6 j = ((ha31_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha31_0_6_contains (j : Fin 7) : (ha31_0_6 j).Contains (fullFactor false 31 6 ((j.val:ℝ)/6)) := by
  rw [ha31_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_5 j) false 31 5 j (ha31_0_5_contains j)
lemma ha31_0_7_eq (j : Fin 7) : ha31_0_7 j = ((ha31_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha31_0_7_contains (j : Fin 7) : (ha31_0_7 j).Contains (fullFactor false 31 7 ((j.val:ℝ)/6)) := by
  rw [ha31_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_6 j) false 31 6 j (ha31_0_6_contains j)
lemma hk31_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_8 j i k).Contains (fullFactor false 31 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 8 (power31_contains j i k) (mpower0_8_contains_g j i k)
lemma ha31_0_8_eq (j : Fin 7) : ha31_0_8 j = ((ha31_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha31_0_8_contains (j : Fin 7) : (ha31_0_8 j).Contains (fullFactor false 31 8 ((j.val:ℝ)/6)) := by
  rw [ha31_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_7 j) false 31 7 j (ha31_0_7_contains j)
lemma ha31_1_0_eq (j : Fin 7) : ha31_1_0 j = atomKernel31_0 j := by fin_cases j <;> decide +kernel
lemma ha31_1_0_contains (j : Fin 7) : (ha31_1_0 j).Contains (fullFactor true 31 0 ((j.val:ℝ)/6)) := by
  rw [ha31_1_0_eq]
  simpa only [fullFactor,ite_true, if_true] using atomKernel31_0_contains j
lemma ha31_1_1_eq (j : Fin 7) : ha31_1_1 j = ((ha31_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha31_1_1_contains (j : Fin 7) : (ha31_1_1 j).Contains (fullFactor true 31 1 ((j.val:ℝ)/6)) := by
  rw [ha31_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_0 j) true 31 0 j (ha31_1_0_contains j)
lemma ha31_1_2_eq (j : Fin 7) : ha31_1_2 j = ((ha31_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha31_1_2_contains (j : Fin 7) : (ha31_1_2 j).Contains (fullFactor true 31 2 ((j.val:ℝ)/6)) := by
  rw [ha31_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_1 j) true 31 1 j (ha31_1_1_contains j)
lemma ha31_1_3_eq (j : Fin 7) : ha31_1_3 j = ((ha31_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha31_1_3_contains (j : Fin 7) : (ha31_1_3 j).Contains (fullFactor true 31 3 ((j.val:ℝ)/6)) := by
  rw [ha31_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_2 j) true 31 2 j (ha31_1_2_contains j)
lemma ha31_1_4_eq (j : Fin 7) : ha31_1_4 j = ((ha31_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha31_1_4_contains (j : Fin 7) : (ha31_1_4 j).Contains (fullFactor true 31 4 ((j.val:ℝ)/6)) := by
  rw [ha31_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_3 j) true 31 3 j (ha31_1_3_contains j)
lemma ha31_1_5_eq (j : Fin 7) : ha31_1_5 j = ((ha31_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha31_1_5_contains (j : Fin 7) : (ha31_1_5 j).Contains (fullFactor true 31 5 ((j.val:ℝ)/6)) := by
  rw [ha31_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_4 j) true 31 4 j (ha31_1_4_contains j)
lemma hk31_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_6 j i k).Contains (fullFactor true 31 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 6 (kernel31_0_contains_g j i k) (mpower1_6_contains j i k)
lemma ha31_1_6_eq (j : Fin 7) : ha31_1_6 j = ((ha31_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha31_1_6_contains (j : Fin 7) : (ha31_1_6 j).Contains (fullFactor true 31 6 ((j.val:ℝ)/6)) := by
  rw [ha31_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_5 j) true 31 5 j (ha31_1_5_contains j)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock31_1
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
namespace hm31_0_0_8
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox density0 hk31_0_8 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 31 8) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk31_0_8 (tableDensity false) (fullFactor false 31 8) density0_contains_g hk31_0_8_contains
lemma atomChecked : tableAtomBox false ha31_0_8 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 31 8) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha31_0_8 31 8 ha31_0_8_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 31 8) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm31_0_0_8
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock31_10
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
namespace hm31_1_1_6
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox density1 hk31_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 31 6) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density1 hk31_1_6 (tableDensity true) (fullFactor true 31 6) density1_contains_g hk31_1_6_contains
lemma atomChecked : tableAtomBox true ha31_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 31 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha31_1_6 31 6 ha31_1_6_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 31 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm31_1_1_6
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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MixedBound31
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
lemma mixed_31_8 : transformTaylor 8 31/((Nat.factorial 8):ℝ)≤(1595574541314512198583916129:ℝ)/1000000000000000000000000000000 := by
  first | (simp [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

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
namespace N0_left
lemma t4_checked : ((hm31_0_0_6.realAnswer).add hm31_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
lemma t4_contains : t4.Contains (sourcePower false 31 (-3/2) 2 4) := by
  rw [← t4_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm31_0_0_6.realContains_g hm31_1_1_6.realContains) (-81) 16 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
lemma tr6_contains : tr6.Contains (fullMoment true true 31 8) := by
  apply RBox.contains_of_abs_g (fullMoment_transformed_cap true 8 31 mixed_31_8) <;> norm_num [tr6,precision]
lemma t6_checked : ((hm31_0_0_8.realAnswer).add tr6).scale (-729) 64=t6 := by decide +kernel
lemma t6_contains : t6.Contains (sourcePower false 31 (-3/2) 2 6) := by
  rw [← t6_checked]
  convert RBox.contains_scale_g (RBox.contains_add_g hm31_0_0_8.realContains tr6_contains) (-729) 64 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [sourcePower,normalizedH]
lemma t12_contains : t12.Contains (sourcePower false 31 (-3/2) 2 12) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 12 coarse_31_14_g) <;> norm_num [t12,precision]
lemma t13_contains : t13.Contains (sourcePower false 31 (-3/2) 2 13) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 13 coarse_31_15_g) <;> norm_num [t13,precision]
lemma t14_contains : t14.Contains (sourcePower false 31 (-3/2) 2 14) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 14 coarse_31_16_g) <;> norm_num [t14,precision]
lemma t15_contains : t15.Contains (sourcePower false 31 (-3/2) 2 15) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 15 coarse_31_17_g) <;> norm_num [t15,precision]
lemma t16_contains : t16.Contains (sourcePower false 31 (-3/2) 2 16) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 16 coarse_31_18_g) <;> norm_num [t16,precision]
lemma t17_contains : t17.Contains (sourcePower false 31 (-3/2) 2 17) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 17 coarse_31_19_g) <;> norm_num [t17,precision]
lemma t18_contains : t18.Contains (sourcePower false 31 (-3/2) 2 18) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 18 coarse_31_20_g) <;> norm_num [t18,precision]
lemma t19_contains : t19.Contains (sourcePower false 31 (-3/2) 2 19) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 19 coarse_31_21_g) <;> norm_num [t19,precision]
lemma t20_contains : t20.Contains (sourcePower false 31 (-3/2) 2 20) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 20 coarse_31_22_g) <;> norm_num [t20,precision]
lemma t21_contains : t21.Contains (sourcePower false 31 (-3/2) 2 21) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 21 coarse_31_23_g) <;> norm_num [t21,precision]
lemma t22_contains : t22.Contains (sourcePower false 31 (-3/2) 2 22) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 22 coarse_31_24_g) <;> norm_num [t22,precision]
lemma t23_contains : t23.Contains (sourcePower false 31 (-3/2) 2 23) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 23 coarse_31_25_g) <;> norm_num [t23,precision]
lemma t24_contains : t24.Contains (sourcePower false 31 (-3/2) 2 24) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 24 coarse_31_26_g) <;> norm_num [t24,precision]
lemma t25_contains : t25.Contains (sourcePower false 31 (-3/2) 2 25) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 25 coarse_31_27_g) <;> norm_num [t25,precision]
lemma t26_contains : t26.Contains (sourcePower false 31 (-3/2) 2 26) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 26 coarse_31_28_g) <;> norm_num [t26,precision]
lemma t27_contains : t27.Contains (sourcePower false 31 (-3/2) 2 27) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 27 coarse_31_29_g) <;> norm_num [t27,precision]
lemma t28_contains : t28.Contains (sourcePower false 31 (-3/2) 2 28) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g false 31 (-3/2) 2 28 coarse_31_30_g) <;> norm_num [t28,precision]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower false 31 (-3/2) 2 r.val) := by
  fin_cases r
  · exact t0_contains_g
  · exact t1_contains_g
  · exact t2_contains_g
  · exact t3_contains_g
  · exact t4_contains
  · exact t5_contains_g
  · exact t6_contains
  · exact t7_contains_g
  · exact t8_contains_g
  · exact t9_contains_g
  · exact t10_contains_g
  · exact t11_contains_g
  · exact t12_contains
  · exact t13_contains
  · exact t14_contains
  · exact t15_contains
  · exact t16_contains
  · exact t17_contains
  · exact t18_contains
  · exact t19_contains
  · exact t20_contains
  · exact t21_contains
  · exact t22_contains
  · exact t23_contains
  · exact t24_contains
  · exact t25_contains
  · exact t26_contains
  · exact t27_contains
  · exact t28_contains
lemma bound0 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound1 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound2 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound3 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound4 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound5 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound6 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound7 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound8 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound9 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound10 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound11 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound12 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound13 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound14 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound15 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound16 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound17 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound18 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound19 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound20 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound21 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound22 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound23 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound24 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound25 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound26 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound27 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound28 : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 9) (v := 1000) (bernsteinBox_contains_g ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<1000) (by decide +kernel)
lemma bound_g_oai (k : Fin 29) : (9:ℝ)/1000<powerToBernstein 28 (sourcePower false 31 (-3/2) 2) k.val := by
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
end N0_left
end SharpPlanar.Bernstein31

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein31.N0_left.bound_g_oai := @OAI.SharpPlanar.Bernstein31.N0_left.bound_g_oai
