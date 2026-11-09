-- Prove2me | solution 1 for OAI.SharpPlanar.Residual79.bound0_1_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:25:58.836548+00:00
-- url     : https://prove2.me/submissions/ba1ec03f-942c-42be-b1e7-d8cdef7c8e25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G383
import Definitions.Def_OAIQ098G411
import Definitions.Def_OAIQ098G1445
import Definitions.Def_OAIQ098G1583
import Definitions.Def_OAIQ098G1629
import Definitions.Def_OAIQ098G1666
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1693
import Definitions.Def_OAIQ098G1696
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel79_0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_kernel79_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_trans78_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_transStep_contains_g
import Theorems.Thm_OAI_SharpPlanar_D_0_g
import Theorems.Thm_OAI_SharpPlanar_D_1_g
import Theorems.Thm_OAI_SharpPlanar_D_3_g
import Theorems.Thm_OAI_SharpPlanar_D_4_g
import Theorems.Thm_OAI_SharpPlanar_D_7_g
import Theorems.Thm_OAI_SharpPlanar_D_9_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerGrid_gridRows_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_abs_bound_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_precision_pos_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g
import Theorems.Thm_OAI_SharpPlanar_piece_interval_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma denominator_ne (t : ℝ) : (t : ℂ) + Complex.I * h ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at hh
  exact (ne_of_gt h_pos_g) hh

lemma continuous_lambda : Continuous lambda := by
  unfold lambda
  fun_prop (disch := intro t; exact mul_ne_zero (by exact_mod_cast b_pos_g.ne') (denominator_ne t))

lemma continuous_z : Continuous z := by
  unfold z
  fun_prop (disch := intro t; exact denominator_ne t)

lemma continuous_kernelMoment (ell : ℕ) (s : ℝ) : Continuous (kernelMoment ell s) := by
  unfold kernelMoment
  exact (continuous_lambda.mul ((continuous_const.mul continuous_z).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul continuous_z).mul continuous_const))

lemma piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * kernelMoment ell s t) volume
      ((j : ℝ)/6) (((j : ℝ)+1)/6) := by
  exact ((continuousOn_density_g p j).mul (continuous_kernelMoment ell s).continuousOn).mono
    (fun _ ht => piece_interval_g hj ht) |>.intervalIntegrable

end SharpPlanar

end OAI
end

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

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_transformed_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (Complex.I*Real.pi*z t*n)))
    (hq : q.Contains (Complex.exp (Complex.I*Real.pi*z t))) :
    (p.mul q).Contains (Complex.exp (Complex.I*Real.pi*z t*(n+1))) := by
  have hh := CBox.contains_mul_g hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end SharpPlanar.IntegerBasis

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
lemma atomKernel79_0_eq (j : Fin 7) : atomKernel79_0 j = kernel0Box (atomPoints j) 79 := by
  fin_cases j <;> decide +kernel
lemma atomKernel79_0_contains (j : Fin 7) : (atomKernel79_0 j).Contains
    (complexTransformedFactor 79 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel79_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=79) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
lemma atomKernel79_1_eq (j : Fin 7) : atomKernel79_1 j = (kernel0Box (atomPoints j) 79).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel79_1_contains (j : Fin 7) : (atomKernel79_1 j).Contains
    (complexTransformedFactor 79 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel79_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=79) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal_g ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq_g] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal_g,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul_g h0 (CBox.contains_mul_g piI_contains_g hz)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers80
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
lemma trans79_r0_0_eq : ∀ k : Fin 16, trans79Expr 0 0 k = trans79_r0_0 k := by decide +kernel
lemma trans79_r0_1_eq : ∀ k : Fin 16, trans79Expr 0 1 k = trans79_r0_1 k := by decide +kernel
lemma trans79_r0_2_eq : ∀ k : Fin 16, trans79Expr 0 2 k = trans79_r0_2 k := by decide +kernel
lemma trans79_r0_3_eq : ∀ k : Fin 16, trans79Expr 0 3 k = trans79_r0_3 k := by decide +kernel
lemma trans79_r0_4_eq : ∀ k : Fin 16, trans79Expr 0 4 k = trans79_r0_4 k := by decide +kernel
lemma trans79_r0_5_eq : ∀ k : Fin 16, trans79Expr 0 5 k = trans79_r0_5 k := by decide +kernel
lemma trans79_r0_6_eq : ∀ k : Fin 16, trans79Expr 0 6 k = trans79_r0_6 k := by decide +kernel
lemma trans79_r0_7_eq : ∀ k : Fin 16, trans79Expr 0 7 k = trans79_r0_7 k := by decide +kernel
lemma trans79_r0_8_eq : ∀ k : Fin 16, trans79Expr 0 8 k = trans79_r0_8 k := by decide +kernel
lemma trans79_r0_9_eq : ∀ k : Fin 16, trans79Expr 0 9 k = trans79_r0_9 k := by decide +kernel
lemma trans79_r0_10_eq : ∀ k : Fin 16, trans79Expr 0 10 k = trans79_r0_10 k := by decide +kernel
lemma trans79_r0_11_eq : ∀ k : Fin 16, trans79Expr 0 11 k = trans79_r0_11 k := by decide +kernel
lemma trans79_r0_12_eq : ∀ k : Fin 16, trans79Expr 0 12 k = trans79_r0_12 k := by decide +kernel
lemma trans79_r0_13_eq : ∀ k : Fin 16, trans79Expr 0 13 k = trans79_r0_13 k := by decide +kernel
lemma trans79_r0_14_eq : ∀ k : Fin 16, trans79Expr 0 14 k = trans79_r0_14 k := by decide +kernel
lemma trans79_r0_15_eq : ∀ k : Fin 16, trans79Expr 0 15 k = trans79_r0_15 k := by decide +kernel
lemma trans79_r0_eq (i k : Fin 16) : trans79Expr 0 i k = trans79_r0 i k := by
  fin_cases i
  · exact trans79_r0_0_eq k
  · exact trans79_r0_1_eq k
  · exact trans79_r0_2_eq k
  · exact trans79_r0_3_eq k
  · exact trans79_r0_4_eq k
  · exact trans79_r0_5_eq k
  · exact trans79_r0_6_eq k
  · exact trans79_r0_7_eq k
  · exact trans79_r0_8_eq k
  · exact trans79_r0_9_eq k
  · exact trans79_r0_10_eq k
  · exact trans79_r0_11_eq k
  · exact trans79_r0_12_eq k
  · exact trans79_r0_13_eq k
  · exact trans79_r0_14_eq k
  · exact trans79_r0_15_eq k
lemma trans79_r1_0_eq : ∀ k : Fin 16, trans79Expr 1 0 k = trans79_r1_0 k := by decide +kernel
lemma trans79_r1_1_eq : ∀ k : Fin 16, trans79Expr 1 1 k = trans79_r1_1 k := by decide +kernel
lemma trans79_r1_2_eq : ∀ k : Fin 16, trans79Expr 1 2 k = trans79_r1_2 k := by decide +kernel
lemma trans79_r1_3_eq : ∀ k : Fin 16, trans79Expr 1 3 k = trans79_r1_3 k := by decide +kernel
lemma trans79_r1_4_eq : ∀ k : Fin 16, trans79Expr 1 4 k = trans79_r1_4 k := by decide +kernel
lemma trans79_r1_5_eq : ∀ k : Fin 16, trans79Expr 1 5 k = trans79_r1_5 k := by decide +kernel
lemma trans79_r1_6_eq : ∀ k : Fin 16, trans79Expr 1 6 k = trans79_r1_6 k := by decide +kernel
lemma trans79_r1_7_eq : ∀ k : Fin 16, trans79Expr 1 7 k = trans79_r1_7 k := by decide +kernel
lemma trans79_r1_8_eq : ∀ k : Fin 16, trans79Expr 1 8 k = trans79_r1_8 k := by decide +kernel
lemma trans79_r1_9_eq : ∀ k : Fin 16, trans79Expr 1 9 k = trans79_r1_9 k := by decide +kernel
lemma trans79_r1_10_eq : ∀ k : Fin 16, trans79Expr 1 10 k = trans79_r1_10 k := by decide +kernel
lemma trans79_r1_11_eq : ∀ k : Fin 16, trans79Expr 1 11 k = trans79_r1_11 k := by decide +kernel
lemma trans79_r1_12_eq : ∀ k : Fin 16, trans79Expr 1 12 k = trans79_r1_12 k := by decide +kernel
lemma trans79_r1_13_eq : ∀ k : Fin 16, trans79Expr 1 13 k = trans79_r1_13 k := by decide +kernel
lemma trans79_r1_14_eq : ∀ k : Fin 16, trans79Expr 1 14 k = trans79_r1_14 k := by decide +kernel
lemma trans79_r1_15_eq : ∀ k : Fin 16, trans79Expr 1 15 k = trans79_r1_15 k := by decide +kernel
lemma trans79_r1_eq (i k : Fin 16) : trans79Expr 1 i k = trans79_r1 i k := by
  fin_cases i
  · exact trans79_r1_0_eq k
  · exact trans79_r1_1_eq k
  · exact trans79_r1_2_eq k
  · exact trans79_r1_3_eq k
  · exact trans79_r1_4_eq k
  · exact trans79_r1_5_eq k
  · exact trans79_r1_6_eq k
  · exact trans79_r1_7_eq k
  · exact trans79_r1_8_eq k
  · exact trans79_r1_9_eq k
  · exact trans79_r1_10_eq k
  · exact trans79_r1_11_eq k
  · exact trans79_r1_12_eq k
  · exact trans79_r1_13_eq k
  · exact trans79_r1_14_eq k
  · exact trans79_r1_15_eq k
lemma trans79_r2_0_eq : ∀ k : Fin 16, trans79Expr 2 0 k = trans79_r2_0 k := by decide +kernel
lemma trans79_r2_1_eq : ∀ k : Fin 16, trans79Expr 2 1 k = trans79_r2_1 k := by decide +kernel
lemma trans79_r2_2_eq : ∀ k : Fin 16, trans79Expr 2 2 k = trans79_r2_2 k := by decide +kernel
lemma trans79_r2_3_eq : ∀ k : Fin 16, trans79Expr 2 3 k = trans79_r2_3 k := by decide +kernel
lemma trans79_r2_4_eq : ∀ k : Fin 16, trans79Expr 2 4 k = trans79_r2_4 k := by decide +kernel
lemma trans79_r2_5_eq : ∀ k : Fin 16, trans79Expr 2 5 k = trans79_r2_5 k := by decide +kernel
lemma trans79_r2_6_eq : ∀ k : Fin 16, trans79Expr 2 6 k = trans79_r2_6 k := by decide +kernel
lemma trans79_r2_7_eq : ∀ k : Fin 16, trans79Expr 2 7 k = trans79_r2_7 k := by decide +kernel
lemma trans79_r2_8_eq : ∀ k : Fin 16, trans79Expr 2 8 k = trans79_r2_8 k := by decide +kernel
lemma trans79_r2_9_eq : ∀ k : Fin 16, trans79Expr 2 9 k = trans79_r2_9 k := by decide +kernel
lemma trans79_r2_10_eq : ∀ k : Fin 16, trans79Expr 2 10 k = trans79_r2_10 k := by decide +kernel
lemma trans79_r2_11_eq : ∀ k : Fin 16, trans79Expr 2 11 k = trans79_r2_11 k := by decide +kernel
lemma trans79_r2_12_eq : ∀ k : Fin 16, trans79Expr 2 12 k = trans79_r2_12 k := by decide +kernel
lemma trans79_r2_13_eq : ∀ k : Fin 16, trans79Expr 2 13 k = trans79_r2_13 k := by decide +kernel
lemma trans79_r2_14_eq : ∀ k : Fin 16, trans79Expr 2 14 k = trans79_r2_14 k := by decide +kernel
lemma trans79_r2_15_eq : ∀ k : Fin 16, trans79Expr 2 15 k = trans79_r2_15 k := by decide +kernel
lemma trans79_r2_eq (i k : Fin 16) : trans79Expr 2 i k = trans79_r2 i k := by
  fin_cases i
  · exact trans79_r2_0_eq k
  · exact trans79_r2_1_eq k
  · exact trans79_r2_2_eq k
  · exact trans79_r2_3_eq k
  · exact trans79_r2_4_eq k
  · exact trans79_r2_5_eq k
  · exact trans79_r2_6_eq k
  · exact trans79_r2_7_eq k
  · exact trans79_r2_8_eq k
  · exact trans79_r2_9_eq k
  · exact trans79_r2_10_eq k
  · exact trans79_r2_11_eq k
  · exact trans79_r2_12_eq k
  · exact trans79_r2_13_eq k
  · exact trans79_r2_14_eq k
  · exact trans79_r2_15_eq k
lemma trans79_r3_0_eq : ∀ k : Fin 16, trans79Expr 3 0 k = trans79_r3_0 k := by decide +kernel
lemma trans79_r3_1_eq : ∀ k : Fin 16, trans79Expr 3 1 k = trans79_r3_1 k := by decide +kernel
lemma trans79_r3_2_eq : ∀ k : Fin 16, trans79Expr 3 2 k = trans79_r3_2 k := by decide +kernel
lemma trans79_r3_3_eq : ∀ k : Fin 16, trans79Expr 3 3 k = trans79_r3_3 k := by decide +kernel
lemma trans79_r3_4_eq : ∀ k : Fin 16, trans79Expr 3 4 k = trans79_r3_4 k := by decide +kernel
lemma trans79_r3_5_eq : ∀ k : Fin 16, trans79Expr 3 5 k = trans79_r3_5 k := by decide +kernel
lemma trans79_r3_6_eq : ∀ k : Fin 16, trans79Expr 3 6 k = trans79_r3_6 k := by decide +kernel
lemma trans79_r3_7_eq : ∀ k : Fin 16, trans79Expr 3 7 k = trans79_r3_7 k := by decide +kernel
lemma trans79_r3_8_eq : ∀ k : Fin 16, trans79Expr 3 8 k = trans79_r3_8 k := by decide +kernel
lemma trans79_r3_9_eq : ∀ k : Fin 16, trans79Expr 3 9 k = trans79_r3_9 k := by decide +kernel
lemma trans79_r3_10_eq : ∀ k : Fin 16, trans79Expr 3 10 k = trans79_r3_10 k := by decide +kernel
lemma trans79_r3_11_eq : ∀ k : Fin 16, trans79Expr 3 11 k = trans79_r3_11 k := by decide +kernel
lemma trans79_r3_12_eq : ∀ k : Fin 16, trans79Expr 3 12 k = trans79_r3_12 k := by decide +kernel
lemma trans79_r3_13_eq : ∀ k : Fin 16, trans79Expr 3 13 k = trans79_r3_13 k := by decide +kernel
lemma trans79_r3_14_eq : ∀ k : Fin 16, trans79Expr 3 14 k = trans79_r3_14 k := by decide +kernel
lemma trans79_r3_15_eq : ∀ k : Fin 16, trans79Expr 3 15 k = trans79_r3_15 k := by decide +kernel
lemma trans79_r3_eq (i k : Fin 16) : trans79Expr 3 i k = trans79_r3 i k := by
  fin_cases i
  · exact trans79_r3_0_eq k
  · exact trans79_r3_1_eq k
  · exact trans79_r3_2_eq k
  · exact trans79_r3_3_eq k
  · exact trans79_r3_4_eq k
  · exact trans79_r3_5_eq k
  · exact trans79_r3_6_eq k
  · exact trans79_r3_7_eq k
  · exact trans79_r3_8_eq k
  · exact trans79_r3_9_eq k
  · exact trans79_r3_10_eq k
  · exact trans79_r3_11_eq k
  · exact trans79_r3_12_eq k
  · exact trans79_r3_13_eq k
  · exact trans79_r3_14_eq k
  · exact trans79_r3_15_eq k
lemma trans79_r4_0_eq : ∀ k : Fin 16, trans79Expr 4 0 k = trans79_r4_0 k := by decide +kernel
lemma trans79_r4_1_eq : ∀ k : Fin 16, trans79Expr 4 1 k = trans79_r4_1 k := by decide +kernel
lemma trans79_r4_2_eq : ∀ k : Fin 16, trans79Expr 4 2 k = trans79_r4_2 k := by decide +kernel
lemma trans79_r4_3_eq : ∀ k : Fin 16, trans79Expr 4 3 k = trans79_r4_3 k := by decide +kernel
lemma trans79_r4_4_eq : ∀ k : Fin 16, trans79Expr 4 4 k = trans79_r4_4 k := by decide +kernel
lemma trans79_r4_5_eq : ∀ k : Fin 16, trans79Expr 4 5 k = trans79_r4_5 k := by decide +kernel
lemma trans79_r4_6_eq : ∀ k : Fin 16, trans79Expr 4 6 k = trans79_r4_6 k := by decide +kernel
lemma trans79_r4_7_eq : ∀ k : Fin 16, trans79Expr 4 7 k = trans79_r4_7 k := by decide +kernel
lemma trans79_r4_8_eq : ∀ k : Fin 16, trans79Expr 4 8 k = trans79_r4_8 k := by decide +kernel
lemma trans79_r4_9_eq : ∀ k : Fin 16, trans79Expr 4 9 k = trans79_r4_9 k := by decide +kernel
lemma trans79_r4_10_eq : ∀ k : Fin 16, trans79Expr 4 10 k = trans79_r4_10 k := by decide +kernel
lemma trans79_r4_11_eq : ∀ k : Fin 16, trans79Expr 4 11 k = trans79_r4_11 k := by decide +kernel
lemma trans79_r4_12_eq : ∀ k : Fin 16, trans79Expr 4 12 k = trans79_r4_12 k := by decide +kernel
lemma trans79_r4_13_eq : ∀ k : Fin 16, trans79Expr 4 13 k = trans79_r4_13 k := by decide +kernel
lemma trans79_r4_14_eq : ∀ k : Fin 16, trans79Expr 4 14 k = trans79_r4_14 k := by decide +kernel
lemma trans79_r4_15_eq : ∀ k : Fin 16, trans79Expr 4 15 k = trans79_r4_15 k := by decide +kernel
lemma trans79_r4_eq (i k : Fin 16) : trans79Expr 4 i k = trans79_r4 i k := by
  fin_cases i
  · exact trans79_r4_0_eq k
  · exact trans79_r4_1_eq k
  · exact trans79_r4_2_eq k
  · exact trans79_r4_3_eq k
  · exact trans79_r4_4_eq k
  · exact trans79_r4_5_eq k
  · exact trans79_r4_6_eq k
  · exact trans79_r4_7_eq k
  · exact trans79_r4_8_eq k
  · exact trans79_r4_9_eq k
  · exact trans79_r4_10_eq k
  · exact trans79_r4_11_eq k
  · exact trans79_r4_12_eq k
  · exact trans79_r4_13_eq k
  · exact trans79_r4_14_eq k
  · exact trans79_r4_15_eq k
lemma trans79_r5_0_eq : ∀ k : Fin 16, trans79Expr 5 0 k = trans79_r5_0 k := by decide +kernel
lemma trans79_r5_1_eq : ∀ k : Fin 16, trans79Expr 5 1 k = trans79_r5_1 k := by decide +kernel
lemma trans79_r5_2_eq : ∀ k : Fin 16, trans79Expr 5 2 k = trans79_r5_2 k := by decide +kernel
lemma trans79_r5_3_eq : ∀ k : Fin 16, trans79Expr 5 3 k = trans79_r5_3 k := by decide +kernel
lemma trans79_r5_4_eq : ∀ k : Fin 16, trans79Expr 5 4 k = trans79_r5_4 k := by decide +kernel
lemma trans79_r5_5_eq : ∀ k : Fin 16, trans79Expr 5 5 k = trans79_r5_5 k := by decide +kernel
lemma trans79_r5_6_eq : ∀ k : Fin 16, trans79Expr 5 6 k = trans79_r5_6 k := by decide +kernel
lemma trans79_r5_7_eq : ∀ k : Fin 16, trans79Expr 5 7 k = trans79_r5_7 k := by decide +kernel
lemma trans79_r5_8_eq : ∀ k : Fin 16, trans79Expr 5 8 k = trans79_r5_8 k := by decide +kernel
lemma trans79_r5_9_eq : ∀ k : Fin 16, trans79Expr 5 9 k = trans79_r5_9 k := by decide +kernel
lemma trans79_r5_10_eq : ∀ k : Fin 16, trans79Expr 5 10 k = trans79_r5_10 k := by decide +kernel
lemma trans79_r5_11_eq : ∀ k : Fin 16, trans79Expr 5 11 k = trans79_r5_11 k := by decide +kernel
lemma trans79_r5_12_eq : ∀ k : Fin 16, trans79Expr 5 12 k = trans79_r5_12 k := by decide +kernel
lemma trans79_r5_13_eq : ∀ k : Fin 16, trans79Expr 5 13 k = trans79_r5_13 k := by decide +kernel
lemma trans79_r5_14_eq : ∀ k : Fin 16, trans79Expr 5 14 k = trans79_r5_14 k := by decide +kernel
lemma trans79_r5_15_eq : ∀ k : Fin 16, trans79Expr 5 15 k = trans79_r5_15 k := by decide +kernel
lemma trans79_r5_eq (i k : Fin 16) : trans79Expr 5 i k = trans79_r5 i k := by
  fin_cases i
  · exact trans79_r5_0_eq k
  · exact trans79_r5_1_eq k
  · exact trans79_r5_2_eq k
  · exact trans79_r5_3_eq k
  · exact trans79_r5_4_eq k
  · exact trans79_r5_5_eq k
  · exact trans79_r5_6_eq k
  · exact trans79_r5_7_eq k
  · exact trans79_r5_8_eq k
  · exact trans79_r5_9_eq k
  · exact trans79_r5_10_eq k
  · exact trans79_r5_11_eq k
  · exact trans79_r5_12_eq k
  · exact trans79_r5_13_eq k
  · exact trans79_r5_14_eq k
  · exact trans79_r5_15_eq k
lemma trans79_eq (j : Fin 6) (i k : Fin 16) : trans79Expr j i k = trans79 j i k := by
  fin_cases j
  · exact trans79_r0_eq i k
  · exact trans79_r1_eq i k
  · exact trans79_r2_eq i k
  · exact trans79_r3_eq i k
  · exact trans79_r4_eq i k
  · exact trans79_r5_eq i k
lemma trans79_contains (j : Fin 6) (i k : Fin 16) :
    (trans79 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(79:ℕ))) := by
  rw [← trans79_eq]
  unfold trans79Expr
  convert exp_transformed_step (trans78_contains_g j i k) (transStep_contains_g j i k) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues80
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
lemma kernel79_0_contains (j : Fin 6) (i k : Fin 16) :
    (kernel79_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(79:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel79_0_eq_g]
  unfold kernel79_0Expr
  have hl := (gridRows_contains_g j i k).2.1
  rw [pointLambda_eq_g] at hl
  have hh := CBox.contains_mul_g hl (trans79_contains j i k)
  simpa only [Bool.false_eq_true,ite_false, if_false,mul_one] using hh
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma dSmall_contains : dSmall.Contains (Real.pi*(3+2*b)/18) := by
  have hb := RBox.contains_add_g (RBox.contains_rat_g 3 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g 2 1 (by norm_num))
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dOther_contains : dOther.Contains (Real.pi*(3-2*b)/18) := by
  have hb := RBox.contains_add_g (RBox.contains_rat_g 3 1 (by norm_num))
    (RBox.contains_scale_g bBounds_contains_g (-2) 1 (by norm_num))
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g hb) 1 18 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)
lemma dBase_contains : dBase.Contains (7*Real.pi*b/9) := by
  convert RBox.contains_scale_g (RBox.contains_mul_g piBounds_contains_g bBounds_contains_g) 7 9 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [qSmall,qLarge,dSmall,dOther,dBase,b] <;> ring)

lemma dBox_contains (n : ℕ) (hn : n%12 ∈ residues) : (dBox n).Contains (D n) := by
  have hh : D n = D (n%12) := by simp [D]
  rw [hh]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn|hn|hn|hn|hn|hn
  · simpa [D_0_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dBase_contains
  · simpa [D_1_g,hn,dBox] using dSmall_contains
  · simpa [D_3_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dSmall_contains
  · simpa [D_4_g,hn,dBox] using dBase_contains
  · simpa [D_7_g,hn,dBox,neg_mul,neg_div] using RBox.neg_contains_g dOther_contains
  · simpa [D_9_g,hn,dBox] using dOther_contains

end Numerical
end SharpPlanar

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments79
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

namespace tm1_79_0
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
lemma checked : cachedMomentRuleBox density1 kernel79_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 79 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using @tableRule_contains_bridge true 79 false density1 kernel79_0
    density1_contains_g kernel79_0_contains
lemma atomChecked : tableAtomBox true atomKernel79_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 79 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel79_0_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 79 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_79_0

namespace tm1_79_1
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
lemma checked : cachedMomentRuleBox density1 kernel79_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 79 1) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] using @tableRule_contains_bridge true 79 true density1 kernel79_1
    density1_contains_g kernel79_1_contains_g
lemma atomChecked : tableAtomBox true atomKernel79_1 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 79 1) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel79_1_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 79 1) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_79_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DataSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed and summable parts of cardinal data

Splitting cardinal data separates the fixed coefficients from the absolutely summable interpolation unknowns.
-/

namespace SharpPlanar
open MeasureTheory
lemma density_split (p : CardinalData) (j : ℕ) (t : ℝ) :
    density p j t = density (fixedPart p) j t+density (positiveData p.x) j t := by
  simp only [density,fixedPart,positiveData,lp.coeFn_zero,Pi.zero_apply,
    Complex.ofReal_zero,zero_mul,zero_add,tsum_zero,add_zero]
lemma K_split (p : CardinalData) (ell : ℕ) (s : ℝ) :
    K p ell s = K (fixedPart p) ell s+K (positiveData p.x) ell s := by
  have hp (j : ℕ) (hj : j<6) :
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t*kernelMoment ell s t) =
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (fixedPart p) j t*kernelMoment ell s t)+
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t*kernelMoment ell s t) := by
    rw [← intervalIntegral.integral_add (piece_integrable _ ell j hj s) (piece_integrable _ ell j hj s)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [density_split,add_mul]
  unfold K
  simp only [fixedPart,positiveData,Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Complex.add_re,add_assoc,← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact hp j (Finset.mem_range.mp hj)
lemma K_fixed₁ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₁ x) ell s=K (fixed₁ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma K_fixed₂ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₂ x) ell s=K (fixed₂ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma transformedJets_fixed₁ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₁ x) ni=transformedJets (fixed₁ 0) ni + S x ni := by
  change _=transformedJets (fixed₁ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₁ x 0 _,K_fixed₁ x 1 _]; ring
  · rw [K_fixed₁ x 0 _]; ring
lemma transformedJets_fixed₂ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₂ x) ni=transformedJets (fixed₂ 0) ni + S x ni := by
  change _=transformedJets (fixed₂ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₂ x 0 _,K_fixed₂ x 1 _]; ring
  · rw [K_fixed₂ x 0 _]; ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Jets of the exact cardinal interpolants

The exact interpolation equations give value and derivative contacts on the triangular shell radii.
-/

namespace SharpPlanar
lemma contactList_apply (n : Node) (d : Bool) :
    contactList (n,d)=if n.val=1 ∧ d=true then 1 else 0 := by
  classical
  unfold contactList columnVector
  rw [lp.single_apply]
  by_cases hn : n.val=1
  · have he : n=firstNode := Subtype.ext hn
    subst n
    cases d <;> simp [firstNode]
  · have he : n≠firstNode := by intro hh; exact hn (congrArg Subtype.val hh)
    simp [hn,he]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableList
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
open Numerical
lemma tableList_apply (a : Bool) (ni : Node×Bool) :
    tableList a ni = if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ) := rfl
lemma tableData_false : tableData false=fixed₁ (tableList false) := by
  simp [tableData,tableConstant,tableC,tableD,fixed₁]
lemma tableData_true : tableData true=fixed₂ (tableList true) := by
  simp [tableData,tableConstant,tableC,tableD,fixed₂]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ResidualBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residuals of the cardinal interpolation equations

The finite coefficient families have small residuals in the exact interpolation equations.
-/

namespace SharpPlanar
open Numerical IntegerIntervals
lemma tableResidual_apply (a : Bool) (n : Node) (d : Bool) :
    tableResidual a (n,d)=
      (if d then (tableD a n.val:ℝ) else (tableC a n.val:ℝ))-
      transformedJets (tableData (!a)) (n,d)+
      (if a=false ∧ n.val=1 ∧ d=true then 1 else 0) := by
  cases a
  · have h := transformedJets_fixed₂ (tableList true) (n,d)
    rw [← tableData_true] at h
    change tableList false (n,d)-S (tableList true) (n,d)-
      (transformedJets (fixed₂ 0) (n,d)-contactList (n,d))=_
    rw [tableList_apply,contactList_apply]
    simp only [Bool.not_false,true_and]
    rw [h]
    ring
  · have h := transformedJets_fixed₁ (tableList false) (n,d)
    rw [← tableData_false] at h
    change tableList true (n,d)-S (tableList false) (n,d)-
      transformedJets (fixed₁ 0) (n,d)=_
    rw [tableList_apply]
    simp only [Bool.not_true,Bool.true_eq_false,false_and,ite_false, if_false,add_zero]
    rw [h]
    ring
lemma tableResidual_deriv (a : Bool) (n : Node) :
    tableResidual a (n,true)=(tableD a n.val:ℝ)+
      (if a=false ∧ n.val=1 then 1 else 0)+
      (tableMomentK (!a) n.val 1-D n.val*tableMomentK (!a) n.val 0)/(Q n.val) := by
  rw [tableResidual_apply]
  simp only [transformedJets,ite_true, if_true,and_true,tableMomentK_eq_g,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one]
  ring
lemma RBox.abs_lt {a : RBox} {x : ℝ} {u v : ℤ} (hx : a.Contains x)
    (hv : 0<v) (hc : a.bound*v<precision*u) : |x|<(u:ℝ)/v := by
  have h1 := RBox.abs_bound_g hx
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have h2 : (a.bound:ℝ)*v < (precision:ℝ)*u := by exact_mod_cast hc
  apply (mul_lt_mul_iff_right₀ precision_pos_g).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact (mul_le_mul_of_nonneg_right h1 hv'.le).trans_lt h2
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual79
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

namespace SharpPlanar.Residual79
open IntegerIntervals IntegerBasis Numerical CachedData
lemma contains0_1 : box0_1.Contains (tableResidual false (node,true)) := by
  rw [tableResidual_deriv]
  have hv := RBox.contains_rat_g (19) 10000000000 (by norm_num)
  have hq := qiBox_contains_g 79 (by norm_num [residues])
  have hd := dBox_contains 79 (by norm_num [residues])
  have hh := RBox.contains_add_g hv (RBox.contains_mul_g (RBox.contains_add_g tm1_79_1.KContains (RBox.neg_contains_g (RBox.contains_mul_g hd tm1_79_0.KContains))) hq)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [box0_1,node,tableC,tableD,tableRaw,div_eq_mul_inv,sub_eq_add_neg])
lemma bound0_1_g_oai : |tableResidual false (node,true)| < (1:ℝ)/10^9 := by
  simpa only [Int.cast_one,Int.cast_pow,Int.cast_ofNat] using RBox.abs_lt (u := 1) contains0_1 (by norm_num : (0:ℤ)<10^9) (by decide +kernel)
end SharpPlanar.Residual79

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Residual79.bound0_1_g_oai := @OAI.SharpPlanar.Residual79.bound0_1_g_oai
