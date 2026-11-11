-- Prove2me | solution 1 for OAI.SharpPlanar.exactLeft_origin_positive_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:00:40.301367+00:00
-- url     : https://prove2.me/submissions/fb2f877a-6e56-4ddf-ae6d-da751eebe402

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G408
import Definitions.Def_OAIQ098G608
import Definitions.Def_OAIQ098G743
import Definitions.Def_OAIQ098G744
import Definitions.Def_OAIQ098G1405
import Definitions.Def_OAIQ098G1652
import Definitions.Def_OAIQ098G1679
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1687
import Definitions.Def_OAIQ098G1693
import Definitions.Def_OAIQ098G1695
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm0_1_0_0_realContains_g
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
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_interpolation_exists_unique_g
import Theorems.Thm_OAI_SharpPlanar_Q_0_g
import Theorems.Thm_OAI_SharpPlanar_Q_1_g
import Theorems.Thm_OAI_SharpPlanar_Q_3_g
import Theorems.Thm_OAI_SharpPlanar_Q_4_g
import Theorems.Thm_OAI_SharpPlanar_Q_7_g
import Theorems.Thm_OAI_SharpPlanar_Q_9_g
import Theorems.Thm_OAI_SharpPlanar_RBox_lower_lt_g
import Theorems.Thm_OAI_SharpPlanar_X_norm_g
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_g
import Theorems.Thm_OAI_SharpPlanar_directDensity_series_g
import Theorems.Thm_OAI_SharpPlanar_directMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_error_zero_cap_g
import Theorems.Thm_OAI_SharpPlanar_fullMoment_direct_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g
import Theorems.Thm_OAI_SharpPlanar_piece_interval_g
import Theorems.Thm_OAI_SharpPlanar_realSpectral_norm_g
import Theorems.Thm_OAI_SharpPlanar_summand_bound_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_trig_table_g
import Theorems.Thm_OAI_SharpPlanar_u_bound_g
import Theorems.Thm_OAI_SharpPlanar_v_bound_g

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

theorem B_eq_inv_b_sq : B = (b ^ 2)⁻¹ := by rw [b_sq_g]; norm_num [B]

theorem z_im (t : ℝ) : (z t).im = h * (B / (t ^ 2 + h ^ 2) - 1) := by
  simp [z, Complex.div_im, Complex.normSq, pow_two]
  ring

theorem strict_damping {t : ℝ} (ht : |t| ≤ 1) : (26 : ℝ) / 435 ≤ (z t).im := by
  rw [z_im]
  have ht2 : t ^ 2 ≤ 1 := by
    have := sq_le_sq₀ (abs_nonneg t) (show (0 : ℝ) ≤ 1 by norm_num)
    simpa using this.mpr ht
  have hd : 0 < t ^ 2 + h ^ 2 := by unfold h; positivity
  have hb : (4 : ℝ) / 3 / ((29 : ℝ) / 25) ≤ B / (t ^ 2 + h ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4/3) hd
    change t ^ 2 + (2/5 : ℝ) ^ 2 ≤ 29/25
    linarith
  unfold h at *
  norm_num at hb ⊢
  linarith



theorem B_pos : 0 < B := by norm_num [B]

theorem imaginary_gaussian_denominator (t : ℝ) :
    h ≤ ‖(t : ℂ) + Complex.I * (h : ℂ)‖ := by
  have hh := Complex.abs_im_le_norm ((t : ℂ) + Complex.I * (h : ℂ))
  simpa [abs_of_pos h_pos_g] using hh

theorem lambda_bound (t : ℝ) : ‖lambda t‖ ≤ 1 / (b * h) := by
  rw [lambda, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos b_pos_g]
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos b_pos_g h_pos_g)
  exact mul_le_mul_of_nonneg_left (imaginary_gaussian_denominator t) b_pos_g.le

theorem z_bound (t : ℝ) : ‖z t‖ ≤ B / h + h := by
  have hden : 0 < ‖(t : ℂ) + Complex.I * (h : ℂ)‖ :=
    h_pos_g.trans_le (imaginary_gaussian_denominator t)
  calc
    ‖z t‖ ≤ ‖-(B : ℂ) / ((t : ℂ) + Complex.I * (h : ℂ))‖ +
      ‖Complex.I * (h : ℂ)‖ := norm_sub_le _ _
    _ = B / ‖(t : ℂ) + Complex.I * (h : ℂ)‖ + h := by
      simp [Complex.norm_real, abs_of_pos B_pos, abs_of_pos h_pos_g]
    _ ≤ B / h + h := add_le_add
      (div_le_div_of_nonneg_left B_pos.le h_pos_g (imaginary_gaussian_denominator t)) le_rfl

theorem kappa_pos : 0 < kappa := by unfold kappa; positivity


theorem kernelMoment_bound (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : |t| ≤ 1) :
    ‖kernelMoment ell s t‖ ≤ (1 / (b*h)) * (Real.pi * (B/h+h))^ell *
      Real.exp (-kappa*s) := by
  have hex : ‖Complex.exp (Complex.I * Real.pi * z t * s)‖ ≤
      Real.exp (-kappa*s) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_sub,
      sub_zero, zero_add]
    have hd := strict_damping ht
    dsimp [kappa]
    nlinarith [mul_nonneg Real.pi_pos.le hs]
  unfold kernelMoment
  rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  have hb' := b_pos_g
  have hh' := h_pos_g
  have hB' := B_pos
  have hl := lambda_bound t
  have hz := z_bound t
  gcongr


lemma densityBound_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity

lemma v_bound' (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ densityBound := by
  apply (v_bound_g n j ht).trans
  unfold densityBound
  nlinarith [Real.pi_gt_three]

lemma density_bound (p : CardinalData) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖density p j t‖ ≤ densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => summand_bound_g p.x n j ht)
    exact (X_summable_pairs_g p.x).mul_left densityBound
  have hsum : ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)‖ ≤ densityBound * ‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityBound * (|p.x (n, false)| + |p.x (n, true)|) :=
        hnorm.tsum_le_tsum (fun n => summand_bound_g p.x n j ht)
          ((X_summable_pairs_g p.x).mul_left densityBound)
      _ = densityBound * ‖p.x‖ := by rw [tsum_mul_left, ← X_norm_g]
  unfold density
  calc
    _ ≤ ‖(p.c₀ : ℂ) * u 0 j t‖ + ‖(p.d₀ : ℂ) * v 0 j t‖ +
      ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| * densityBound + |p.d₀| * densityBound + densityBound * ‖p.x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exacts [u_bound_g _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring


lemma continuous_u (n j : ℕ) : Continuous (u n j) := by
  unfold u
  fun_prop

lemma continuous_v (n j : ℕ) : Continuous (v n j) := by
  unfold v
  fun_prop

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


lemma residue_lt {a : ℕ} (ha : a ∈ residues) : a < 12 := by
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

lemma Q_pos (n : ℕ) : 0 < Q n := by
  unfold Q
  apply mul_pos (sq_pos_of_pos (by positivity))
  apply Finset.prod_pos
  intro a ha
  have hane : a ≠ n % 12 := (Finset.mem_erase.mp ha).1
  have hal : a < 12 := residue_lt (Finset.mem_erase.mp ha).2
  have hnl : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hh1 : (-12 : ℝ) < ((n % 12 : ℕ) : ℝ) - a := by
    have ha' : (a : ℝ) < 12 := by exact_mod_cast hal
    have hn' : (0 : ℝ) ≤ ((n % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hh2 : (((n % 12 : ℕ) : ℝ) - a) < 12 := by
    have hn' : ((n % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast hnl
    have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have hs : Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - a) / 12) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < ((n%12 : ℕ):ℝ)-a+12)])
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < 12-(((n%12 : ℕ):ℝ)-a))])]
    apply div_ne_zero
    · apply mul_ne_zero Real.pi_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hane)
    · norm_num
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hs)

lemma Q_mod (n : ℕ) : Q (n % 12) = Q n := by simp [Q]
lemma D_mod (n : ℕ) : D (n % 12) = D n := by simp [D]

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
lemma atomKernel0_0_eq (j : Fin 7) : atomKernel0_0 j = kernel0Box (atomPoints j) 0 := by
  fin_cases j <;> decide +kernel
lemma atomKernel0_0_contains (j : Fin 7) : (atomKernel0_0 j).Contains
    (complexTransformedFactor 0 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel0_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=0) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
lemma trans0_contains (j : Fin 6) (i k : Fin 16) :
    (trans0 j i k).Contains (Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(0:ℕ))) := by
  simpa only [trans0,Nat.cast_zero,mul_zero,Complex.exp_zero,Int.cast_one,one_div,inv_one,Int.cast_zero,zero_div,mul_zero,zero_mul,add_zero] using
    (CBox.contains_rat_g 1 1 0 1 (by norm_num) (by norm_num))
end SharpPlanar.CachedData

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
lemma kernel0_0_r0_0_eq : ∀ k : Fin 16, kernel0_0Expr 0 0 k = kernel0_0_r0_0 k := by decide +kernel
lemma kernel0_0_r0_1_eq : ∀ k : Fin 16, kernel0_0Expr 0 1 k = kernel0_0_r0_1 k := by decide +kernel
lemma kernel0_0_r0_2_eq : ∀ k : Fin 16, kernel0_0Expr 0 2 k = kernel0_0_r0_2 k := by decide +kernel
lemma kernel0_0_r0_3_eq : ∀ k : Fin 16, kernel0_0Expr 0 3 k = kernel0_0_r0_3 k := by decide +kernel
lemma kernel0_0_r0_4_eq : ∀ k : Fin 16, kernel0_0Expr 0 4 k = kernel0_0_r0_4 k := by decide +kernel
lemma kernel0_0_r0_5_eq : ∀ k : Fin 16, kernel0_0Expr 0 5 k = kernel0_0_r0_5 k := by decide +kernel
lemma kernel0_0_r0_6_eq : ∀ k : Fin 16, kernel0_0Expr 0 6 k = kernel0_0_r0_6 k := by decide +kernel
lemma kernel0_0_r0_7_eq : ∀ k : Fin 16, kernel0_0Expr 0 7 k = kernel0_0_r0_7 k := by decide +kernel
lemma kernel0_0_r0_8_eq : ∀ k : Fin 16, kernel0_0Expr 0 8 k = kernel0_0_r0_8 k := by decide +kernel
lemma kernel0_0_r0_9_eq : ∀ k : Fin 16, kernel0_0Expr 0 9 k = kernel0_0_r0_9 k := by decide +kernel
lemma kernel0_0_r0_10_eq : ∀ k : Fin 16, kernel0_0Expr 0 10 k = kernel0_0_r0_10 k := by decide +kernel
lemma kernel0_0_r0_11_eq : ∀ k : Fin 16, kernel0_0Expr 0 11 k = kernel0_0_r0_11 k := by decide +kernel
lemma kernel0_0_r0_12_eq : ∀ k : Fin 16, kernel0_0Expr 0 12 k = kernel0_0_r0_12 k := by decide +kernel
lemma kernel0_0_r0_13_eq : ∀ k : Fin 16, kernel0_0Expr 0 13 k = kernel0_0_r0_13 k := by decide +kernel
lemma kernel0_0_r0_14_eq : ∀ k : Fin 16, kernel0_0Expr 0 14 k = kernel0_0_r0_14 k := by decide +kernel
lemma kernel0_0_r0_15_eq : ∀ k : Fin 16, kernel0_0Expr 0 15 k = kernel0_0_r0_15 k := by decide +kernel
lemma kernel0_0_r0_eq (i k : Fin 16) : kernel0_0Expr 0 i k = kernel0_0_r0 i k := by
  fin_cases i
  · exact kernel0_0_r0_0_eq k
  · exact kernel0_0_r0_1_eq k
  · exact kernel0_0_r0_2_eq k
  · exact kernel0_0_r0_3_eq k
  · exact kernel0_0_r0_4_eq k
  · exact kernel0_0_r0_5_eq k
  · exact kernel0_0_r0_6_eq k
  · exact kernel0_0_r0_7_eq k
  · exact kernel0_0_r0_8_eq k
  · exact kernel0_0_r0_9_eq k
  · exact kernel0_0_r0_10_eq k
  · exact kernel0_0_r0_11_eq k
  · exact kernel0_0_r0_12_eq k
  · exact kernel0_0_r0_13_eq k
  · exact kernel0_0_r0_14_eq k
  · exact kernel0_0_r0_15_eq k
lemma kernel0_0_r1_0_eq : ∀ k : Fin 16, kernel0_0Expr 1 0 k = kernel0_0_r1_0 k := by decide +kernel
lemma kernel0_0_r1_1_eq : ∀ k : Fin 16, kernel0_0Expr 1 1 k = kernel0_0_r1_1 k := by decide +kernel
lemma kernel0_0_r1_2_eq : ∀ k : Fin 16, kernel0_0Expr 1 2 k = kernel0_0_r1_2 k := by decide +kernel
lemma kernel0_0_r1_3_eq : ∀ k : Fin 16, kernel0_0Expr 1 3 k = kernel0_0_r1_3 k := by decide +kernel
lemma kernel0_0_r1_4_eq : ∀ k : Fin 16, kernel0_0Expr 1 4 k = kernel0_0_r1_4 k := by decide +kernel
lemma kernel0_0_r1_5_eq : ∀ k : Fin 16, kernel0_0Expr 1 5 k = kernel0_0_r1_5 k := by decide +kernel
lemma kernel0_0_r1_6_eq : ∀ k : Fin 16, kernel0_0Expr 1 6 k = kernel0_0_r1_6 k := by decide +kernel
lemma kernel0_0_r1_7_eq : ∀ k : Fin 16, kernel0_0Expr 1 7 k = kernel0_0_r1_7 k := by decide +kernel
lemma kernel0_0_r1_8_eq : ∀ k : Fin 16, kernel0_0Expr 1 8 k = kernel0_0_r1_8 k := by decide +kernel
lemma kernel0_0_r1_9_eq : ∀ k : Fin 16, kernel0_0Expr 1 9 k = kernel0_0_r1_9 k := by decide +kernel
lemma kernel0_0_r1_10_eq : ∀ k : Fin 16, kernel0_0Expr 1 10 k = kernel0_0_r1_10 k := by decide +kernel
lemma kernel0_0_r1_11_eq : ∀ k : Fin 16, kernel0_0Expr 1 11 k = kernel0_0_r1_11 k := by decide +kernel
lemma kernel0_0_r1_12_eq : ∀ k : Fin 16, kernel0_0Expr 1 12 k = kernel0_0_r1_12 k := by decide +kernel
lemma kernel0_0_r1_13_eq : ∀ k : Fin 16, kernel0_0Expr 1 13 k = kernel0_0_r1_13 k := by decide +kernel
lemma kernel0_0_r1_14_eq : ∀ k : Fin 16, kernel0_0Expr 1 14 k = kernel0_0_r1_14 k := by decide +kernel
lemma kernel0_0_r1_15_eq : ∀ k : Fin 16, kernel0_0Expr 1 15 k = kernel0_0_r1_15 k := by decide +kernel
lemma kernel0_0_r1_eq (i k : Fin 16) : kernel0_0Expr 1 i k = kernel0_0_r1 i k := by
  fin_cases i
  · exact kernel0_0_r1_0_eq k
  · exact kernel0_0_r1_1_eq k
  · exact kernel0_0_r1_2_eq k
  · exact kernel0_0_r1_3_eq k
  · exact kernel0_0_r1_4_eq k
  · exact kernel0_0_r1_5_eq k
  · exact kernel0_0_r1_6_eq k
  · exact kernel0_0_r1_7_eq k
  · exact kernel0_0_r1_8_eq k
  · exact kernel0_0_r1_9_eq k
  · exact kernel0_0_r1_10_eq k
  · exact kernel0_0_r1_11_eq k
  · exact kernel0_0_r1_12_eq k
  · exact kernel0_0_r1_13_eq k
  · exact kernel0_0_r1_14_eq k
  · exact kernel0_0_r1_15_eq k
lemma kernel0_0_r2_0_eq : ∀ k : Fin 16, kernel0_0Expr 2 0 k = kernel0_0_r2_0 k := by decide +kernel
lemma kernel0_0_r2_1_eq : ∀ k : Fin 16, kernel0_0Expr 2 1 k = kernel0_0_r2_1 k := by decide +kernel
lemma kernel0_0_r2_2_eq : ∀ k : Fin 16, kernel0_0Expr 2 2 k = kernel0_0_r2_2 k := by decide +kernel
lemma kernel0_0_r2_3_eq : ∀ k : Fin 16, kernel0_0Expr 2 3 k = kernel0_0_r2_3 k := by decide +kernel
lemma kernel0_0_r2_4_eq : ∀ k : Fin 16, kernel0_0Expr 2 4 k = kernel0_0_r2_4 k := by decide +kernel
lemma kernel0_0_r2_5_eq : ∀ k : Fin 16, kernel0_0Expr 2 5 k = kernel0_0_r2_5 k := by decide +kernel
lemma kernel0_0_r2_6_eq : ∀ k : Fin 16, kernel0_0Expr 2 6 k = kernel0_0_r2_6 k := by decide +kernel
lemma kernel0_0_r2_7_eq : ∀ k : Fin 16, kernel0_0Expr 2 7 k = kernel0_0_r2_7 k := by decide +kernel
lemma kernel0_0_r2_8_eq : ∀ k : Fin 16, kernel0_0Expr 2 8 k = kernel0_0_r2_8 k := by decide +kernel
lemma kernel0_0_r2_9_eq : ∀ k : Fin 16, kernel0_0Expr 2 9 k = kernel0_0_r2_9 k := by decide +kernel
lemma kernel0_0_r2_10_eq : ∀ k : Fin 16, kernel0_0Expr 2 10 k = kernel0_0_r2_10 k := by decide +kernel
lemma kernel0_0_r2_11_eq : ∀ k : Fin 16, kernel0_0Expr 2 11 k = kernel0_0_r2_11 k := by decide +kernel
lemma kernel0_0_r2_12_eq : ∀ k : Fin 16, kernel0_0Expr 2 12 k = kernel0_0_r2_12 k := by decide +kernel
lemma kernel0_0_r2_13_eq : ∀ k : Fin 16, kernel0_0Expr 2 13 k = kernel0_0_r2_13 k := by decide +kernel
lemma kernel0_0_r2_14_eq : ∀ k : Fin 16, kernel0_0Expr 2 14 k = kernel0_0_r2_14 k := by decide +kernel
lemma kernel0_0_r2_15_eq : ∀ k : Fin 16, kernel0_0Expr 2 15 k = kernel0_0_r2_15 k := by decide +kernel
lemma kernel0_0_r2_eq (i k : Fin 16) : kernel0_0Expr 2 i k = kernel0_0_r2 i k := by
  fin_cases i
  · exact kernel0_0_r2_0_eq k
  · exact kernel0_0_r2_1_eq k
  · exact kernel0_0_r2_2_eq k
  · exact kernel0_0_r2_3_eq k
  · exact kernel0_0_r2_4_eq k
  · exact kernel0_0_r2_5_eq k
  · exact kernel0_0_r2_6_eq k
  · exact kernel0_0_r2_7_eq k
  · exact kernel0_0_r2_8_eq k
  · exact kernel0_0_r2_9_eq k
  · exact kernel0_0_r2_10_eq k
  · exact kernel0_0_r2_11_eq k
  · exact kernel0_0_r2_12_eq k
  · exact kernel0_0_r2_13_eq k
  · exact kernel0_0_r2_14_eq k
  · exact kernel0_0_r2_15_eq k
lemma kernel0_0_r3_0_eq : ∀ k : Fin 16, kernel0_0Expr 3 0 k = kernel0_0_r3_0 k := by decide +kernel
lemma kernel0_0_r3_1_eq : ∀ k : Fin 16, kernel0_0Expr 3 1 k = kernel0_0_r3_1 k := by decide +kernel
lemma kernel0_0_r3_2_eq : ∀ k : Fin 16, kernel0_0Expr 3 2 k = kernel0_0_r3_2 k := by decide +kernel
lemma kernel0_0_r3_3_eq : ∀ k : Fin 16, kernel0_0Expr 3 3 k = kernel0_0_r3_3 k := by decide +kernel
lemma kernel0_0_r3_4_eq : ∀ k : Fin 16, kernel0_0Expr 3 4 k = kernel0_0_r3_4 k := by decide +kernel
lemma kernel0_0_r3_5_eq : ∀ k : Fin 16, kernel0_0Expr 3 5 k = kernel0_0_r3_5 k := by decide +kernel
lemma kernel0_0_r3_6_eq : ∀ k : Fin 16, kernel0_0Expr 3 6 k = kernel0_0_r3_6 k := by decide +kernel
lemma kernel0_0_r3_7_eq : ∀ k : Fin 16, kernel0_0Expr 3 7 k = kernel0_0_r3_7 k := by decide +kernel
lemma kernel0_0_r3_8_eq : ∀ k : Fin 16, kernel0_0Expr 3 8 k = kernel0_0_r3_8 k := by decide +kernel
lemma kernel0_0_r3_9_eq : ∀ k : Fin 16, kernel0_0Expr 3 9 k = kernel0_0_r3_9 k := by decide +kernel
lemma kernel0_0_r3_10_eq : ∀ k : Fin 16, kernel0_0Expr 3 10 k = kernel0_0_r3_10 k := by decide +kernel
lemma kernel0_0_r3_11_eq : ∀ k : Fin 16, kernel0_0Expr 3 11 k = kernel0_0_r3_11 k := by decide +kernel
lemma kernel0_0_r3_12_eq : ∀ k : Fin 16, kernel0_0Expr 3 12 k = kernel0_0_r3_12 k := by decide +kernel
lemma kernel0_0_r3_13_eq : ∀ k : Fin 16, kernel0_0Expr 3 13 k = kernel0_0_r3_13 k := by decide +kernel
lemma kernel0_0_r3_14_eq : ∀ k : Fin 16, kernel0_0Expr 3 14 k = kernel0_0_r3_14 k := by decide +kernel
lemma kernel0_0_r3_15_eq : ∀ k : Fin 16, kernel0_0Expr 3 15 k = kernel0_0_r3_15 k := by decide +kernel
lemma kernel0_0_r3_eq (i k : Fin 16) : kernel0_0Expr 3 i k = kernel0_0_r3 i k := by
  fin_cases i
  · exact kernel0_0_r3_0_eq k
  · exact kernel0_0_r3_1_eq k
  · exact kernel0_0_r3_2_eq k
  · exact kernel0_0_r3_3_eq k
  · exact kernel0_0_r3_4_eq k
  · exact kernel0_0_r3_5_eq k
  · exact kernel0_0_r3_6_eq k
  · exact kernel0_0_r3_7_eq k
  · exact kernel0_0_r3_8_eq k
  · exact kernel0_0_r3_9_eq k
  · exact kernel0_0_r3_10_eq k
  · exact kernel0_0_r3_11_eq k
  · exact kernel0_0_r3_12_eq k
  · exact kernel0_0_r3_13_eq k
  · exact kernel0_0_r3_14_eq k
  · exact kernel0_0_r3_15_eq k
lemma kernel0_0_r4_0_eq : ∀ k : Fin 16, kernel0_0Expr 4 0 k = kernel0_0_r4_0 k := by decide +kernel
lemma kernel0_0_r4_1_eq : ∀ k : Fin 16, kernel0_0Expr 4 1 k = kernel0_0_r4_1 k := by decide +kernel
lemma kernel0_0_r4_2_eq : ∀ k : Fin 16, kernel0_0Expr 4 2 k = kernel0_0_r4_2 k := by decide +kernel
lemma kernel0_0_r4_3_eq : ∀ k : Fin 16, kernel0_0Expr 4 3 k = kernel0_0_r4_3 k := by decide +kernel
lemma kernel0_0_r4_4_eq : ∀ k : Fin 16, kernel0_0Expr 4 4 k = kernel0_0_r4_4 k := by decide +kernel
lemma kernel0_0_r4_5_eq : ∀ k : Fin 16, kernel0_0Expr 4 5 k = kernel0_0_r4_5 k := by decide +kernel
lemma kernel0_0_r4_6_eq : ∀ k : Fin 16, kernel0_0Expr 4 6 k = kernel0_0_r4_6 k := by decide +kernel
lemma kernel0_0_r4_7_eq : ∀ k : Fin 16, kernel0_0Expr 4 7 k = kernel0_0_r4_7 k := by decide +kernel
lemma kernel0_0_r4_8_eq : ∀ k : Fin 16, kernel0_0Expr 4 8 k = kernel0_0_r4_8 k := by decide +kernel
lemma kernel0_0_r4_9_eq : ∀ k : Fin 16, kernel0_0Expr 4 9 k = kernel0_0_r4_9 k := by decide +kernel
lemma kernel0_0_r4_10_eq : ∀ k : Fin 16, kernel0_0Expr 4 10 k = kernel0_0_r4_10 k := by decide +kernel
lemma kernel0_0_r4_11_eq : ∀ k : Fin 16, kernel0_0Expr 4 11 k = kernel0_0_r4_11 k := by decide +kernel
lemma kernel0_0_r4_12_eq : ∀ k : Fin 16, kernel0_0Expr 4 12 k = kernel0_0_r4_12 k := by decide +kernel
lemma kernel0_0_r4_13_eq : ∀ k : Fin 16, kernel0_0Expr 4 13 k = kernel0_0_r4_13 k := by decide +kernel
lemma kernel0_0_r4_14_eq : ∀ k : Fin 16, kernel0_0Expr 4 14 k = kernel0_0_r4_14 k := by decide +kernel
lemma kernel0_0_r4_15_eq : ∀ k : Fin 16, kernel0_0Expr 4 15 k = kernel0_0_r4_15 k := by decide +kernel
lemma kernel0_0_r4_eq (i k : Fin 16) : kernel0_0Expr 4 i k = kernel0_0_r4 i k := by
  fin_cases i
  · exact kernel0_0_r4_0_eq k
  · exact kernel0_0_r4_1_eq k
  · exact kernel0_0_r4_2_eq k
  · exact kernel0_0_r4_3_eq k
  · exact kernel0_0_r4_4_eq k
  · exact kernel0_0_r4_5_eq k
  · exact kernel0_0_r4_6_eq k
  · exact kernel0_0_r4_7_eq k
  · exact kernel0_0_r4_8_eq k
  · exact kernel0_0_r4_9_eq k
  · exact kernel0_0_r4_10_eq k
  · exact kernel0_0_r4_11_eq k
  · exact kernel0_0_r4_12_eq k
  · exact kernel0_0_r4_13_eq k
  · exact kernel0_0_r4_14_eq k
  · exact kernel0_0_r4_15_eq k
lemma kernel0_0_r5_0_eq : ∀ k : Fin 16, kernel0_0Expr 5 0 k = kernel0_0_r5_0 k := by decide +kernel
lemma kernel0_0_r5_1_eq : ∀ k : Fin 16, kernel0_0Expr 5 1 k = kernel0_0_r5_1 k := by decide +kernel
lemma kernel0_0_r5_2_eq : ∀ k : Fin 16, kernel0_0Expr 5 2 k = kernel0_0_r5_2 k := by decide +kernel
lemma kernel0_0_r5_3_eq : ∀ k : Fin 16, kernel0_0Expr 5 3 k = kernel0_0_r5_3 k := by decide +kernel
lemma kernel0_0_r5_4_eq : ∀ k : Fin 16, kernel0_0Expr 5 4 k = kernel0_0_r5_4 k := by decide +kernel
lemma kernel0_0_r5_5_eq : ∀ k : Fin 16, kernel0_0Expr 5 5 k = kernel0_0_r5_5 k := by decide +kernel
lemma kernel0_0_r5_6_eq : ∀ k : Fin 16, kernel0_0Expr 5 6 k = kernel0_0_r5_6 k := by decide +kernel
lemma kernel0_0_r5_7_eq : ∀ k : Fin 16, kernel0_0Expr 5 7 k = kernel0_0_r5_7 k := by decide +kernel
lemma kernel0_0_r5_8_eq : ∀ k : Fin 16, kernel0_0Expr 5 8 k = kernel0_0_r5_8 k := by decide +kernel
lemma kernel0_0_r5_9_eq : ∀ k : Fin 16, kernel0_0Expr 5 9 k = kernel0_0_r5_9 k := by decide +kernel
lemma kernel0_0_r5_10_eq : ∀ k : Fin 16, kernel0_0Expr 5 10 k = kernel0_0_r5_10 k := by decide +kernel
lemma kernel0_0_r5_11_eq : ∀ k : Fin 16, kernel0_0Expr 5 11 k = kernel0_0_r5_11 k := by decide +kernel
lemma kernel0_0_r5_12_eq : ∀ k : Fin 16, kernel0_0Expr 5 12 k = kernel0_0_r5_12 k := by decide +kernel
lemma kernel0_0_r5_13_eq : ∀ k : Fin 16, kernel0_0Expr 5 13 k = kernel0_0_r5_13 k := by decide +kernel
lemma kernel0_0_r5_14_eq : ∀ k : Fin 16, kernel0_0Expr 5 14 k = kernel0_0_r5_14 k := by decide +kernel
lemma kernel0_0_r5_15_eq : ∀ k : Fin 16, kernel0_0Expr 5 15 k = kernel0_0_r5_15 k := by decide +kernel
lemma kernel0_0_r5_eq (i k : Fin 16) : kernel0_0Expr 5 i k = kernel0_0_r5 i k := by
  fin_cases i
  · exact kernel0_0_r5_0_eq k
  · exact kernel0_0_r5_1_eq k
  · exact kernel0_0_r5_2_eq k
  · exact kernel0_0_r5_3_eq k
  · exact kernel0_0_r5_4_eq k
  · exact kernel0_0_r5_5_eq k
  · exact kernel0_0_r5_6_eq k
  · exact kernel0_0_r5_7_eq k
  · exact kernel0_0_r5_8_eq k
  · exact kernel0_0_r5_9_eq k
  · exact kernel0_0_r5_10_eq k
  · exact kernel0_0_r5_11_eq k
  · exact kernel0_0_r5_12_eq k
  · exact kernel0_0_r5_13_eq k
  · exact kernel0_0_r5_14_eq k
  · exact kernel0_0_r5_15_eq k
lemma kernel0_0_eq (j : Fin 6) (i k : Fin 16) : kernel0_0Expr j i k = kernel0_0 j i k := by
  fin_cases j
  · exact kernel0_0_r0_eq i k
  · exact kernel0_0_r1_eq i k
  · exact kernel0_0_r2_eq i k
  · exact kernel0_0_r3_eq i k
  · exact kernel0_0_r4_eq i k
  · exact kernel0_0_r5_eq i k
lemma kernel0_0_contains (j : Fin 6) (i k : Fin 16) :
    (kernel0_0 j i k).Contains (lambda (quadraturePoint j.val (16*i.val+k.val))*
      Complex.exp (Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val))*(0:ℕ))*
      (if false then Complex.I*Real.pi*z (quadraturePoint j.val (16*i.val+k.val)) else 1)) := by
  rw [← kernel0_0_eq]
  unfold kernel0_0Expr
  have hl := (gridRows_contains_g j i k).2.1
  rw [pointLambda_eq_g] at hl
  have hh := CBox.contains_mul_g hl (trans0_contains j i k)
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
lemma momentPower_zero (t : ℂ) : momentPower 0 t = 1 := by simp [momentPower]
lemma momentPower_zero_contains (t : ℂ) : (CBox.rat 1 1 0 1).Contains (momentPower 0 t) := by
  simpa [momentPower_zero] using CBox.contains_rat_g 1 1 0 1 (by norm_num) (by norm_num)
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
lemma mpower1_0_contains (j : Fin 6) (i k : Fin 16) :
    (mpower1_0 j i k).Contains (momentPower 0 (z (quadraturePoint j.val (16*i.val+k.val)))) := momentPower_zero_contains _
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma squared_sine_to_cos (x : ℝ) : (2 * Real.sin x)^2 = 2 - 2*Real.cos (2*x) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq_g]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1

end SharpPlanar

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
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders0
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
lemma hk0_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_0 j i k).Contains (fullFactor true 0 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 0 (kernel0_0_contains j i k) (mpower1_0_contains j i k)
lemma ha0_1_0_eq (j : Fin 7) : ha0_1_0 j = atomKernel0_0 j := by fin_cases j <;> decide +kernel
lemma ha0_1_0_contains (j : Fin 7) : (ha0_1_0 j).Contains (fullFactor true 0 0 ((j.val:ℝ)/6)) := by
  rw [ha0_1_0_eq]
  simpa only [fullFactor,ite_true, if_true] using atomKernel0_0_contains j
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_4
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
namespace hm0_0_1_0
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
lemma checked : cachedMomentRuleBox density0 hk0_1_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 0 0) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk0_1_0 (tableDensity false) (fullFactor true 0 0) density0_contains_g hk0_1_0_contains
lemma atomChecked : tableAtomBox false ha0_1_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 0 0) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha0_1_0 0 0 ha0_1_0_contains
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 0 0) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_1_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoupledFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coupled interpolation system

The finite inverse and tail estimates solve the interpolation equations in the space of absolutely summable coefficients.
-/

namespace SharpPlanar
open Numerical

lemma interpolationInverse_eq (neg : Bool) (r : X) :
    interpolationInverse neg r - signedS neg (interpolationInverse neg r) = r :=
  (Classical.choose_spec (interpolation_exists_unique_g neg r)).1
lemma coupled_equations (g₁ g₂ : X) :
    coupledLeft g₁ g₂-S (coupledRight g₁ g₂)=g₁ ∧
    coupledRight g₁ g₂-S (coupledLeft g₁ g₂)=g₂ := by
  have hp := interpolationInverse_eq false (g₁+g₂)
  have hm := interpolationInverse_eq true (g₁-g₂)
  change interpolationInverse false (g₁+g₂)-S (interpolationInverse false (g₁+g₂))=g₁+g₂ at hp
  change interpolationInverse true (g₁-g₂)- -S (interpolationInverse true (g₁-g₂))=g₁-g₂ at hm
  constructor <;> (apply lp.ext; funext ni)
  all_goals
    have hp' := congrArg (fun x : X => x ni) hp
    have hm' := congrArg (fun x : X => x ni) hm
    simp only [coupledLeft,coupledRight,map_smul,map_add,map_sub,lp.coeFn_sub,lp.coeFn_add,
      lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,lp.coeFn_neg,Pi.neg_apply] at *
    linarith
end SharpPlanar

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
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate

namespace SharpPlanar

lemma weighted_exp_integral (c : ℂ) (hc : c ≠ 0) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((T : ℂ)-t)*Complex.exp (c*t)) =
      (Complex.exp (c*T)-1-c*T)/c^2 := by
  let F : ℝ → ℂ := fun t => (((T : ℂ)-t)*Complex.exp (c*t))/c +
      Complex.exp (c*t)/c^2
  have hd (t : ℝ) : HasDerivAt F (((T : ℂ)-t)*Complex.exp (c*t)) t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (c*t))
        (Complex.exp (c*t)*c) t := by
      convert (((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal).cexp using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
    have ht : HasDerivAt (fun t : ℝ => (T : ℂ)-t) (-1) t := by
      convert ((hasDerivAt_id (t : ℂ)).const_sub (T : ℂ)).comp_ofReal using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
    convert ((ht.mul he).div_const c).add (he.div_const (c^2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (field_simp [hc]; ring)
  have hi : IntervalIntegrable (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (c*t)) volume 0 T :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  simp only [F, Complex.ofReal_zero, sub_self, zero_mul, mul_zero, Complex.exp_zero,
    sub_zero, zero_div]
  field_simp
  ring

lemma exponential_division_one (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1)/(U : ℂ) =
      Complex.I*Real.pi * ∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 1; ring
  rw [he, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

lemma exponential_division_two (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1-Complex.I*Real.pi*T*U)/(U : ℂ)^2 =
      -(Real.pi : ℂ)^2 * ∫ t in (0 : ℝ)..T,
        ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => ((T : ℂ)-t)*Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 2; ring
  rw [he, weighted_exp_integral _ hc]
  have hh : Complex.I*Real.pi*(U : ℂ)*T = Complex.I*Real.pi*T*U := by ring
  rw [hh]
  field_simp
  simp [Complex.I_sq]
  ring

end SharpPlanar

namespace SharpPlanar

lemma triangular_piece_integrals (N : ℕ) (a : ℕ → ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ l, Continuous (f l)) :
    (∑ j ∈ Finset.range N, ∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc 1 N, ∫ t in a 0..a l, f l t := by
  have ht (j : ℕ) : (∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    exact intervalIntegral.integral_finsetSum fun l _ => (hf l).intervalIntegrable _ _
  simp_rw [ht]
  have hswap := Finset.sum_Ico_Ico_comm' 0 (N+1)
    (fun j l => ∫ t in a j..a (j+1), f l t)
  have hi (j : ℕ) : Finset.Ico (j+1) (N+1) = Finset.Icc (j+1) N := by
    ext l
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  simp only [Nat.Ico_zero_eq_range, hi] at hswap
  have hleft : (∑ j ∈ Finset.range (N+1),
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t) =
      ∑ j ∈ Finset.range N,
        ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    rw [Finset.sum_range_succ]
    simp
  rw [hleft] at hswap
  rw [hswap]
  have hadj (l : ℕ) : (∑ j ∈ Finset.range l, ∫ t in a j..a (j+1), f l t) =
      ∫ t in a 0..a l, f l t := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => (hf l).intervalIntegrable _ _)
  simp_rw [hadj]
  symm
  apply Finset.sum_subset
  · intro l hl
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro l hl hn
    have : l = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range, not_and, not_le] at *
      omega
    simp [this]

lemma u_integrand (n j : ℕ) (s t : ℝ) :
    u n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold u
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

lemma v_integrand (n j : ℕ) (s t : ℝ) :
    v n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold v
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (Complex.I*Real.pi*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

end SharpPlanar

namespace SharpPlanar

lemma P_as_table (s : ℝ) : P s =
    ∏ a ∈ residues,
      (2 - 2*(Real.cos (Real.pi*s/6)*cosTable a + Real.sin (Real.pi*s/6)*sinTable a)) := by
  unfold P
  apply Finset.prod_congr rfl
  intro a ha
  rw [squared_sine_to_cos,
    show 2*(Real.pi*(s-a)/12) = Real.pi*s/6-Real.pi*a/6 by ring, Real.cos_sub]
  rw [(trig_table_g a (by have := residue_lt ha; omega)).1,
    (trig_table_g a (by have := residue_lt ha; omega)).2]

end SharpPlanar

namespace SharpPlanar

lemma phase_nat (j : ℕ) (s : ℝ) :
    Complex.exp (Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s) =
      ((Real.cos (Real.pi*s/6) : ℂ) + Real.sin (Real.pi*s/6)*Complex.I)^j := by
  rw [show Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s =
      (j : ℂ) * ((Real.pi*s/6 : ℝ) * Complex.I) by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_ofReal_mul_I]

lemma polynomial_fourier_algebra (c d : ℝ) (hcd : c^2+d^2=1) :
    (∏ a ∈ residues, (2-2*(c*cosTable a+d*sinTable a))) =
    (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*((c : ℂ)+(d : ℂ)*Complex.I)^j).re := by
  have hd2 : d^2 = 1-c^2 := by linarith
  have hd3 : d^3 = (1-c^2)*d := by rw [pow_succ, hd2]
  have hd4 : d^4 = (1-c^2)^2 := by rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, hd2]
  have hd5 : d^5 = (1-c^2)^2*d := by rw [pow_succ, hd4]
  have hd6 : d^6 = (1-c^2)^3 := by rw [show (6 : ℕ) = 2*3 by norm_num, pow_mul, hd2]
  norm_num [residues, cosTable, sinTable, Finset.sum_Icc_succ_top, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring_nf
  simp only [b_sq_g, b_pow_3, hd2, hd3, hd4, hd5, hd6]
  ring


theorem P_fourier (s : ℝ) :
    P s = (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)).re := by
  simp_rw [phase_nat]
  rw [P_as_table]
  exact polynomial_fourier_algebra _ _ (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s/6)])

end SharpPlanar

namespace SharpPlanar

lemma Pmoment_zero (s : ℝ) : Pmoment 0 s = P s := by
  rw [P_fourier]
  simp [Pmoment]

lemma Pmoment_hasDerivAt (ell : ℕ) (s : ℝ) :
    HasDerivAt (Pmoment ell) (Pmoment (ell+1) s) s := by
  have hh (j : ℕ) : HasDerivAt (fun s : ℝ =>
      2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s))
      (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^(ell+1) *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)) s := by
    have he := (((hasDerivAt_id (s : ℂ)).const_mul
      (Complex.I*Real.pi*((j : ℝ)/6 : ℝ))).comp_ofReal).cexp.const_mul
        (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell)
    convert he using 1 <;> first | rfl | (simp only [mul_one, pow_succ, id_eq]; ring)
  have hd := ((hasDerivAt_const s (Pcoeff 0*(0 : ℂ)^ell)).add
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.Icc (1 : ℕ) 6) => hh j)))
  have hdr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd
  convert hdr using 1 <;> first | rfl | simp [Pmoment]

lemma trig_nat_mod12 (n : ℕ) :
    Real.sin (Real.pi*n/6) = sinTable (n%12) ∧
    Real.cos (Real.pi*n/6) = cosTable (n%12) := by
  have hn : (n : ℝ) = (n%12 : ℕ) + 12*(n/12 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 12).symm
  have ha : Real.pi*n/6 = Real.pi*(n%12 : ℕ)/6 + (n/12 : ℕ)*(2*Real.pi) := by
    conv_lhs => rw [hn]
    ring
  rw [ha, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  exact trig_table_g (n%12) (by omega)

lemma Pmoment_mod (ell n : ℕ) : Pmoment ell n = Pmoment ell (n%12 : ℕ) := by
  unfold Pmoment
  simp only [phase_nat]
  rw [(trig_nat_mod12 n).1, (trig_nat_mod12 n).2,
    (trig_table_g (n%12) (by omega)).1, (trig_table_g (n%12) (by omega)).2]


lemma phase_node (j n : ℕ) :
    Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ)) =
      (cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I := by
  rw [show Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ) =
      ((Real.pi*(j*n : ℕ)/6 : ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, (trig_nat_mod12 (j*n)).1, (trig_nat_mod12 (j*n)).2]

lemma Pmoment_node_formula (ell n : ℕ) :
    Pmoment ell n =
      (Pcoeff 0*(0 : ℂ)^ell + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
        2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
          ((cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I)).re := by
  unfold Pmoment
  simp_rw [phase_node]

lemma Pmoment_node_0 :
    Pmoment 0 (0 : ℕ) = 0 ∧ Pmoment 1 (0 : ℕ) = 0 ∧
      Pmoment 2 (0 : ℕ) = 2*Q 0 ∧ Pmoment 3 (0 : ℕ) = 6*Q 0*D 0 := by
  rw [Q_0_g, D_0_g, Pmoment_node_formula 0 0, Pmoment_node_formula 1 0,
    Pmoment_node_formula 2 0, Pmoment_node_formula 3 0]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf

lemma Pmoment_node_1 :
    Pmoment 0 (1 : ℕ) = 0 ∧ Pmoment 1 (1 : ℕ) = 0 ∧
      Pmoment 2 (1 : ℕ) = 2*Q 1 ∧ Pmoment 3 (1 : ℕ) = 6*Q 1*D 1 := by
  rw [Q_1_g, D_1_g, Pmoment_node_formula 0 1, Pmoment_node_formula 1 1,
    Pmoment_node_formula 2 1, Pmoment_node_formula 3 1]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_3 :
    Pmoment 0 (3 : ℕ) = 0 ∧ Pmoment 1 (3 : ℕ) = 0 ∧
      Pmoment 2 (3 : ℕ) = 2*Q 3 ∧ Pmoment 3 (3 : ℕ) = 6*Q 3*D 3 := by
  rw [Q_3_g, D_3_g, Pmoment_node_formula 0 3, Pmoment_node_formula 1 3,
    Pmoment_node_formula 2 3, Pmoment_node_formula 3 3]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_4 :
    Pmoment 0 (4 : ℕ) = 0 ∧ Pmoment 1 (4 : ℕ) = 0 ∧
      Pmoment 2 (4 : ℕ) = 2*Q 4 ∧ Pmoment 3 (4 : ℕ) = 6*Q 4*D 4 := by
  rw [Q_4_g, D_4_g, Pmoment_node_formula 0 4, Pmoment_node_formula 1 4,
    Pmoment_node_formula 2 4, Pmoment_node_formula 3 4]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_7 :
    Pmoment 0 (7 : ℕ) = 0 ∧ Pmoment 1 (7 : ℕ) = 0 ∧
      Pmoment 2 (7 : ℕ) = 2*Q 7 ∧ Pmoment 3 (7 : ℕ) = 6*Q 7*D 7 := by
  rw [Q_7_g, D_7_g, Pmoment_node_formula 0 7, Pmoment_node_formula 1 7,
    Pmoment_node_formula 2 7, Pmoment_node_formula 3 7]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_9 :
    Pmoment 0 (9 : ℕ) = 0 ∧ Pmoment 1 (9 : ℕ) = 0 ∧
      Pmoment 2 (9 : ℕ) = 2*Q 9 ∧ Pmoment 3 (9 : ℕ) = 6*Q 9*D 9 := by
  rw [Q_9_g, D_9_g, Pmoment_node_formula 0 9, Pmoment_node_formula 1 9,
    Pmoment_node_formula 2 9, Pmoment_node_formula 3 9]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring


theorem Pmoment_node_data (n : ℕ) (hn : n%12 ∈ residues) :
    Pmoment 0 n = 0 ∧ Pmoment 1 n = 0 ∧
      Pmoment 2 n = 2*Q n ∧ Pmoment 3 n = 6*Q n*D n := by
  rw [Pmoment_mod 0 n, Pmoment_mod 1 n, Pmoment_mod 2 n, Pmoment_mod 3 n,
    ← Q_mod n, ← D_mod n]
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;> rw [hn]
  · exact Pmoment_node_0
  · exact Pmoment_node_1
  · exact Pmoment_node_3
  · exact Pmoment_node_4
  · exact Pmoment_node_7
  · exact Pmoment_node_9

end SharpPlanar

namespace SharpPlanar

lemma foldedU_unfold (n : ℕ) (s : ℝ) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedU
  simp_rw [u_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))) (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedV_unfold (n : ℕ) (s : ℝ) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedV
  simp_rw [v_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))))
      (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedU_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2)).re := by
  rw [foldedU_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_two (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

lemma foldedV_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ))).re := by
  rw [foldedV_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_one (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he, intervalIntegral.integral_const_mul]


lemma exp_phase_split (T s v : ℝ) :
    Complex.exp (Complex.I*Real.pi*T*v)*
      Complex.exp (Complex.I*Real.pi*T*(s-v)) =
        Complex.exp (Complex.I*Real.pi*T*s) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma foldedU_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = (P s-P n-Pmoment 1 n*(s-n))/(s-n)^2 := by
  rw [foldedU_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)-
        (2*Pcoeff l*(Complex.I*Real.pi*((l:ℝ)/6:ℝ))*
          Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))*(s-n : ℝ))/(s-n : ℝ)^2 := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)-
          (2*Pcoeff l*(Complex.I*Real.pi*(l/6 : ℝ))*
            Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n))*(s-n : ℝ) := by push_cast <;> ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div]
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [P_fourier s, P_fourier n]
  simp [Pmoment, Complex.mul_re]

lemma foldedV_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedV n s = (P s-P n)/(s-n) := by
  rw [foldedV_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ)) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))/(s-n : ℝ) := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n) := by push_cast <;> ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, P_fourier s, P_fourier n]
  simp [Complex.mul_re]

lemma folded_basis_quotients (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = P s/(s-n)^2 ∧ foldedV n s = P s/(s-n) := by
  obtain ⟨h0,h1,-,-⟩ := Pmoment_node_data n hn
  rw [Pmoment_zero] at h0
  rw [foldedU_quotient n s hs, foldedV_quotient n s hs, h0, h1]
  simp

end SharpPlanar



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar

lemma fourierIntegral_temperate {μ : Measure ℝ} (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    {f : ℝ → ℂ} (hf : Integrable f μ)
    (hm : ∀ n : ℕ, Integrable (fun t => ‖t‖^n * ‖f t‖) μ) :
    Function.HasTemperateGrowth (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) := by
  refine ⟨VectorFourier.contDiff_fourierIntegral L (fun n _ => hm n), fun n => ?_⟩
  refine ⟨0, ∫ t, ‖VectorFourier.fourierPowSMulRight L f t n‖ ∂μ, fun s => ?_⟩
  rw [VectorFourier.iteratedFDeriv_fourierIntegral L
    (N := (⊤ : ℕ∞)) (fun n _ => hm n) hf.aestronglyMeasurable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  simpa only [pow_zero, mul_one] using
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 μ L.toLinearMap₁₂
      (fun t => VectorFourier.fourierPowSMulRight L f t n) s

lemma spectral_eq (μ : Measure ℝ) (f : ℝ → ℂ) : spectral μ f =
    VectorFourier.fourierIntegral 𝐞 μ spectralForm.toLinearMap₁₂ f := by
  funext s
  unfold spectral VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with t
  have hL : spectralForm.toLinearMap₁₂ t s = (-1/2 : ℝ)*t*s := by
    change (-1/2 : ℝ)*(t*s) = _
    ring
  rw [hL]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

lemma spectral_temperate {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ)
    (hm : ∀ n : ℕ, Integrable (fun t => ‖t‖^n * ‖f t‖) μ) :
    Function.HasTemperateGrowth (spectral μ f) := by
  rw [spectral_eq]
  exact fourierIntegral_temperate spectralForm hf hm

lemma integrable_moment_Icc {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) (n : ℕ) :
    Integrable (fun t => ‖t‖^n * ‖f t‖) (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn (fun t : ℝ => ‖t‖^n) (Icc a b) := by fun_prop
  exact IntegrableOn.continuousOn_mul hc hf.norm isCompact_Icc

lemma spectral_Icc_temperate {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) :
    Function.HasTemperateGrowth (spectral (volume.restrict (Icc a b)) f) :=
  spectral_temperate hf (integrable_moment_Icc hf)

end SharpPlanar

namespace SharpPlanar

lemma spectral_integrable {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (s : ℝ) :
    Integrable (fun t => Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I)*f t) μ := by
  refine (hf.norm).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun t : ℝ =>
        Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards with t
    simp [Complex.norm_exp]

lemma spectral_hasDerivAt {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (hm : Integrable (fun t => ‖t‖*‖f t‖) μ) (s : ℝ) :
    HasDerivAt (spectral μ f)
      (spectral μ (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) s) s := by
  have hf' : Integrable (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) μ := by
    refine (hm.const_mul Real.pi).mono' ?_ ?_
    · exact (((by fun_prop : Continuous (fun t : ℝ =>
          ((Real.pi*t : ℝ):ℂ)*Complex.I))).aestronglyMeasurable).mul hf.aestronglyMeasurable
    · filter_upwards with t
      simp [abs_of_pos Real.pi_pos, mul_assoc]
  have he (t x : ℝ) : HasDerivAt (fun x : ℝ =>
      Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
      (Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
        (((Real.pi*t : ℝ):ℂ)*Complex.I*f t)) x := by
    convert ((((hasDerivAt_id x).const_mul (Real.pi*t)).ofReal_comp.mul_const
      Complex.I).cexp.mul_const (f t)) using 1 <;> first | rfl | (simp only [mul_one, id_eq]; ring)
  have hr := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (bound := fun t => Real.pi*(‖t‖*‖f t‖))
    (F := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
    (F' := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
      (((Real.pi*t : ℝ):ℂ)*Complex.I*f t))
    (Filter.univ_mem) (Filter.Eventually.of_forall fun x => (spectral_integrable hf x).aestronglyMeasurable)
    (spectral_integrable hf s) (spectral_integrable hf' s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t x _ => by
      simp [Complex.norm_exp, abs_of_pos Real.pi_pos, mul_assoc])
    (hm.const_mul Real.pi) (Filter.Eventually.of_forall fun t x _ => he t x)
  exact hr.2

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma interval_spectral_eq (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (∫ t in a..b, f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f s := by
  unfold spectral
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [mul_comm (f t)]
  congr 1
  congr 1
  push_cast
  ring

lemma interval_exponential_hasDerivAt {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in a..b,
      f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in a..b, f t * (Complex.I*Real.pi*(t:ℂ)) *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
  have hfi : IntegrableOn f (Icc a b) volume := hf.integrableOn_Icc
  have hder := spectral_hasDerivAt hfi (by
    simpa only [pow_one] using integrable_moment_Icc hfi 1) s
  have hfun : (fun s : ℝ => ∫ t in a..b, f t*Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f :=
    funext (interval_spectral_eq f hab)
  rw [hfun]
  convert hder using 1
  all_goals try with_reducible_and_instances rfl
  rw [interval_spectral_eq _ hab]
  congr 1
  funext t
  push_cast
  ring

lemma basisMoment_zero (sec : Bool) (n : ℕ) : basisMoment sec n 0 =
    if sec then foldedV n else foldedU n := by
  cases sec <;> funext s <;> simp [basisMoment,foldedU,foldedV]

lemma basisMoment_hasDerivAt (sec : Bool) (n ell : ℕ) (s : ℝ) :
    HasDerivAt (basisMoment sec n ell) (basisMoment sec n (ell+1) s) s := by
  have hd (j : ℕ) : HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^(ell+1) *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
    convert interval_exponential_hasDerivAt (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)
      (f:=fun t => (if sec then v n j t else u n j t)*(Complex.I*Real.pi*(t:ℂ))^ell)
      (by cases sec <;> apply Continuous.continuousOn <;>
        apply Continuous.mul <;> first | exact continuous_u n j | exact continuous_v n j | fun_prop) s using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext t
    rw [pow_succ]
    ring
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range 6) => hd j))

lemma basisU_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)^2*basisMoment false n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [Bool.false_eq_true,ite_false, if_false]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).1]
    field_simp

lemma basisV_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)*basisMoment true n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [ite_true, if_true]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).2]
    field_simp


lemma P_hasDerivAt (s : ℝ) : HasDerivAt P (Pmoment 1 s) s := by
  simpa only [show Pmoment 0 = P from funext Pmoment_zero] using Pmoment_hasDerivAt 0 s

lemma basisU_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*(s-n)*basisMoment false n 0 s + (s-n)^2*basisMoment false n 1 s = Pmoment 1 s := by
  have hd := (((hasDerivAt_id s).sub_const (n:ℝ)).pow 2).mul
    (basisMoment_hasDerivAt false n 0 s)
  have heq : (fun s : ℝ => (s-n)^2*basisMoment false n 0 s) = P :=
    funext (basisU_factor n hn)
  simp only [Pi.mul_def, Pi.pow_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

lemma basisU_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment false n 0 s + 4*(s-n)*basisMoment false n 1 s +
      (s-n)^2*basisMoment false n 2 s = Pmoment 2 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := ((hl.const_mul 2).mul (basisMoment_hasDerivAt false n 0 s)).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 1 s))
  have heq : (fun s : ℝ => 2*(s-n)*basisMoment false n 0 s +
      (s-n)^2*basisMoment false n 1 s) = Pmoment 1 := funext (basisU_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)

lemma basisU_factor_deriv3 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    6*basisMoment false n 1 s + 6*(s-n)*basisMoment false n 2 s +
      (s-n)^2*basisMoment false n 3 s = Pmoment 3 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := (((basisMoment_hasDerivAt false n 0 s).const_mul 2).add
    ((hl.const_mul 4).mul (basisMoment_hasDerivAt false n 1 s))).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 2 s))
  have heq : (fun s : ℝ => 2*basisMoment false n 0 s +
      4*(s-n)*basisMoment false n 1 s+(s-n)^2*basisMoment false n 2 s) = Pmoment 2 :=
    funext (basisU_factor_deriv2 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 2 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)

lemma basisV_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    basisMoment true n 0 s + (s-n)*basisMoment true n 1 s = Pmoment 1 s := by
  have hd := ((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 0 s)
  have heq : (fun s : ℝ => (s-n)*basisMoment true n 0 s) = P :=
    funext (basisV_factor n hn)
  simp only [Pi.mul_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

lemma basisV_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment true n 1 s + (s-n)*basisMoment true n 2 s = Pmoment 2 s := by
  have hd := (basisMoment_hasDerivAt true n 0 s).add
    (((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 1 s))
  have heq : (fun s : ℝ => basisMoment true n 0 s +
      (s-n)*basisMoment true n 1 s) = Pmoment 1 := funext (basisV_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)


theorem basis_diagonal_jets (n : ℕ) (hn : n%12 ∈ residues) :
    basisMoment false n 0 n = Q n ∧ basisMoment false n 1 n = Q n*D n ∧
    basisMoment true n 0 n = 0 ∧ basisMoment true n 1 n = Q n := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data n hn
  have hu0 := basisU_factor_deriv2 n hn n
  have hu1 := basisU_factor_deriv3 n hn n
  have hv0 := basisV_factor_deriv1 n hn n
  have hv1 := basisV_factor_deriv2 n hn n
  simp only [sub_self,zero_mul,zero_pow (by omega : 2 ≠ 0),add_zero] at hu0 hu1 hv0 hv1
  rw [h1] at hv0
  exact ⟨by linarith,by linarith,hv0,by linarith⟩


theorem basis_off_diagonal_jets (n m : ℕ) (hn : n%12 ∈ residues)
    (hm : m%12 ∈ residues) (hnm : m ≠ n) :
    basisMoment false n 0 m = 0 ∧ basisMoment false n 1 m = 0 ∧
    basisMoment true n 0 m = 0 ∧ basisMoment true n 1 m = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data m hm
  rw [Pmoment_zero] at h0
  have hsub : (m:ℝ)-(n:ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hu0 := basisU_factor n hn m
  have hv0 := basisV_factor n hn m
  rw [h0] at hu0 hv0
  have hu : basisMoment false n 0 m = 0 := (mul_eq_zero.mp hu0).resolve_left (pow_ne_zero 2 hsub)
  have hv : basisMoment true n 0 m = 0 := (mul_eq_zero.mp hv0).resolve_left hsub
  have hu1 := basisU_factor_deriv1 n hn m
  have hv1 := basisV_factor_deriv1 n hn m
  rw [hu,h1,mul_zero,zero_add] at hu1
  rw [hv,h1,zero_add] at hv1
  exact ⟨hu,(mul_eq_zero.mp hu1).resolve_left (pow_ne_zero 2 hsub),
    hv,(mul_eq_zero.mp hv1).resolve_left hsub⟩

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma basisMoment_bound (sec : Bool) (n ell : ℕ) (s : ℝ) :
    |basisMoment sec n ell s| ≤ densityBound * Real.pi^ell := by
  have hj (j : ℕ) (hj : j < 6) :
      ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ densityBound*Real.pi^ell/6 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun t => (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (a:=(j:ℝ)/6) (b:=((j:ℝ)+1)/6) (C:=densityBound*Real.pi^ell) (fun t ht => ?_)
    · convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rw [show ((j:ℝ)+1)/6-(j:ℝ)/6=1/6 by ring,abs_of_pos (by norm_num : (0:ℝ)<1/6)]
      ring
    · rw [mul_assoc,norm_mul]
      apply mul_le_mul _ (realSpectral_norm_g ell (piece_interval_g hj (uIoc_subset_uIcc ht)) s)
        (norm_nonneg _) densityBound_nonneg
      cases sec
      · exact u_bound_g n j (piece_interval_g hj (uIoc_subset_uIcc ht))
      · exact v_bound' n j (piece_interval_g hj (uIoc_subset_uIcc ht))
  unfold basisMoment
  calc
    _ ≤ ‖∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j ∈ Finset.range 6, ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range 6, densityBound*Real.pi^ell/6 := by
      exact Finset.sum_le_sum (fun j hj' => hj j (Finset.mem_range.mp hj'))
    _ = _ := by simp <;> ring

lemma cardinalSeries_summand_bound (p : CardinalData) (ell : ℕ) (s : ℝ) (n : Node) :
    ‖p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s‖ ≤
      (densityBound*Real.pi^ell)*(|p.x (n,false)|+|p.x (n,true)|) := by
  calc
    _ ≤ ‖p.x (n,false)*basisMoment false n.val ell s‖ +
        ‖p.x (n,true)*basisMoment true n.val ell s‖ := norm_add_le _ _
    _ = |p.x (n,false)| * |basisMoment false n.val ell s| +
        |p.x (n,true)| * |basisMoment true n.val ell s| := by simp [norm_mul,Real.norm_eq_abs]
    _ ≤ |p.x (n,false)| * (densityBound*Real.pi^ell)+
        |p.x (n,true)| * (densityBound*Real.pi^ell) := by
      gcongr <;> apply basisMoment_bound
    _ = _ := by ring

lemma cardinalSeries_summable (p : CardinalData) (ell : ℕ) (s : ℝ) :
    Summable (fun n : Node => p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s) :=
  ((X_summable_pairs_g p.x).mul_left (densityBound*Real.pi^ell)).of_norm_bounded
    (cardinalSeries_summand_bound p ell s)

lemma cardinalSeries_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (cardinalSeries p ell) (cardinalSeries p (ell+1) s) s := by
  have hsum := hasDerivAt_tsum
    ((X_summable_pairs_g p.x).mul_left (densityBound*Real.pi^(ell+1)))
    (fun n y => ((basisMoment_hasDerivAt false n.val ell y).const_mul (p.x (n,false))).add
      ((basisMoment_hasDerivAt true n.val ell y).const_mul (p.x (n,true))))
    (fun n y => cardinalSeries_summand_bound p (ell+1) y n)
    (cardinalSeries_summable p ell 0) s
  exact ((((Pmoment_hasDerivAt ell s).const_mul p.C).add
    ((basisMoment_hasDerivAt false 0 ell s).const_mul p.c₀)).add
    ((basisMoment_hasDerivAt true 0 ell s).const_mul p.d₀)).add hsum


lemma cardinalSeries_jets (p : CardinalData) (m : Node) :
    cardinalSeries p 0 m.val = Q m.val * p.x (m,false) ∧
    cardinalSeries p 1 m.val = Q m.val * (D m.val*p.x (m,false)+p.x (m,true)) := by
  obtain ⟨hP0,hP1,-,-⟩ := Pmoment_node_data m.val m.property.2
  obtain ⟨hU0,hU1,hV0,hV1⟩ := basis_diagonal_jets m.val m.property.2
  have hm : m.val ≠ 0 := Nat.ne_of_gt m.property.1
  have hz : 0%12 ∈ residues := by norm_num [residues]
  obtain ⟨hc0,hc1,hd0,hd1⟩ := basis_off_diagonal_jets 0 m.val hz m.property.2 hm
  have hother (n : Node) (hn : n ≠ m) :
      basisMoment false n.val 0 m.val = 0 ∧ basisMoment false n.val 1 m.val = 0 ∧
      basisMoment true n.val 0 m.val = 0 ∧ basisMoment true n.val 1 m.val = 0 := by
    apply basis_off_diagonal_jets n.val m.val n.property.2 m.property.2
    intro he
    exact hn (Subtype.ext he.symm)
  have hs0 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 0 m.val +
      p.x (n,true)*basisMoment true n.val 0 m.val)) = p.x (m,false)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU0,hV0]; ring
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h0,h2]
  have hs1 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 1 m.val +
      p.x (n,true)*basisMoment true n.val 1 m.val)) =
      p.x (m,false)*(Q m.val*D m.val)+p.x (m,true)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU1,hV1]
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h1,h3]
  constructor
  · simp only [cardinalSeries,hP0,hc0,hd0,hs0,mul_zero,zero_add]
    ring
  · simp only [cardinalSeries,hP1,hc1,hd1,hs1,mul_zero,zero_add]
    ring

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

namespace SharpPlanar

lemma expCut_eq (c x : ℝ) (hx : 0 ≤ x) : expCut c x = Real.exp (-c*x) := by
  simp [expCut, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


lemma gaussianSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussianSchwartz c hc x = Real.exp (-c*‖x‖^2) := by
  change expCut c (‖x‖^2) = _
  exact expCut_eq c _ (sq_nonneg _)

end SharpPlanar


open scoped SchwartzMap

namespace SharpPlanar

lemma spectral_dirac_eq (t : ℝ) (c : ℂ) (s : ℝ) :
    spectral (Measure.dirac t) (fun _ => c) s =
      Complex.exp (((Real.pi*t*s : ℝ) : ℂ)*Complex.I) * c := by
  simp [spectral]

lemma spectral_dirac_temperate (t : ℝ) (c : ℂ) :
    Function.HasTemperateGrowth (spectral (Measure.dirac t) (fun _ => c)) := by
  apply spectral_temperate
  · exact integrable_dirac (by finiteness)
  · intro n
    exact integrable_dirac (by finiteness)


lemma cardinal_temperate (p : CardinalData) :
    Function.HasTemperateGrowth (cardinal p) := by
  have h₀ := spectral_dirac_temperate 0 ((p.C : ℂ)*Pcoeff 0)
  have h₁ : Function.HasTemperateGrowth (fun s => ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      spectral (Measure.dirac ((j : ℝ)/6)) (fun _ => 2*(p.C : ℂ)*Pcoeff j) s) := by
    exact Function.HasTemperateGrowth.sum fun j _ => spectral_dirac_temperate _ _
  have h₂ : Function.HasTemperateGrowth (fun s => ∑ j ∈ Finset.range 6,
      spectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) s) := by
    apply Function.HasTemperateGrowth.sum
    intro j hj
    apply spectral_Icc_temperate
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply (continuousOn_density_g p j).mono
    intro t ht
    have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hj0 : (0 : ℝ) ≤ j := by positivity
    constructor <;> linarith [ht.1, ht.2]
  exact Complex.reCLM.hasTemperateGrowth.comp ((h₀.add h₁).add h₂)


lemma radiusCoord_temperate :
    Function.HasTemperateGrowth (fun x : Plane => b*‖x‖^2) := by
  fun_prop

lemma qSchwartz_apply (p : CardinalData) (x : Plane) :
    qSchwartz p x = Real.exp (-Real.pi*h*(b*‖x‖^2)) * cardinal p (b*‖x‖^2) := by
  have hq : Function.HasTemperateGrowth (fun x : Plane => cardinal p (b*‖x‖^2)) :=
    (cardinal_temperate p).comp radiusCoord_temperate
  rw [qSchwartz, SchwartzMap.smulLeftCLM_apply_apply hq, gaussianSchwartz_apply]
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma spectral_interval_direct (p : CardinalData) (j : ℕ) (s : ℝ) :
    spectral (volume.restrict (Icc ((j:ℝ)/6) (((j:ℝ)+1)/6))) (density p j) s =
    ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel 0 s t := by
  rw [spectral,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [directKernel,pow_zero,one_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

lemma cardinal_eq_cardinalSeries (p : CardinalData) (s : ℝ) :
    cardinal p s = cardinalSeries p 0 s := by
  unfold cardinal
  simp_rw [spectral_dirac_eq,spectral_interval_direct]
  have hat : (Complex.exp (((Real.pi*0*s:ℝ):ℂ)*Complex.I)*((p.C:ℂ)*Pcoeff 0) +
      ∑ j ∈ Finset.Icc (1:ℕ) 6,
        Complex.exp (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I)*(2*(p.C:ℂ)*Pcoeff j)) =
      (p.C:ℂ)*(Pcoeff 0 + ∑ j ∈ Finset.Icc (1:ℕ) 6,
        2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j:ℝ)/6)*s)) := by
    simp only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have he : (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I) =
        Complex.I*Real.pi*((j:ℝ)/6)*s := by push_cast <;> ring
    rw [he]
    ring
  rw [hat,Complex.add_re,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [directDensity_series_g]
  simp only [cardinalSeries,Pmoment,pow_zero,mul_one]
  push_cast
  ring

lemma cardinal_hasDerivAt (p : CardinalData) (s : ℝ) :
    HasDerivAt (cardinal p) (cardinalSeries p 1 s) s := by
  simpa only [funext (cardinal_eq_cardinalSeries p)] using cardinalSeries_hasDerivAt p 0 s

lemma cardinal_jets (p : CardinalData) (m : Node) :
    cardinal p m.val = Q m.val*p.x (m,false) ∧
      deriv (cardinal p) m.val = Q m.val*(p.x (m,true)+D m.val*p.x (m,false)) := by
  rcases cardinalSeries_jets p m with ⟨h0,h1⟩
  rw [cardinal_eq_cardinalSeries,h0,(cardinal_hasDerivAt p m.val).deriv]
  exact ⟨rfl,by simpa only [add_comm] using h1⟩

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FixedRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact contact interpolation solution

The inverse interpolation operator determines the coefficient lists for the prescribed contacts.
-/

namespace SharpPlanar
lemma exactLists_equations : exactList₁-S exactList₂=g₁ ∧ exactList₂-S exactList₁=g₂ :=
  coupled_equations g₁ g₂
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_KernelDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped Topology
lemma kernelMoment_hasDerivAt (ell : ℕ) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => kernelMoment ell s t) (kernelMoment (ell+1) s t) s := by
  have hd := ((((hasDerivAt_id s).ofReal_comp.const_mul (Complex.I*Real.pi*z t)).cexp).const_mul
    (lambda t*(Complex.I*Real.pi*z t)^ell))
  simpa only [kernelMoment,pow_succ,Complex.ofReal_one,id_eq,mul_one,one_mul,mul_assoc,
    mul_left_comm,mul_comm] using hd
lemma continuous_joint_kernel (ell : ℕ) :
    Continuous (fun st : ℝ×ℝ => kernelMoment ell st.1 st.2) := by
  unfold kernelMoment
  exact ((continuous_lambda.comp continuous_snd).mul
    ((continuous_const.mul (continuous_z.comp continuous_snd)).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul (continuous_z.comp continuous_snd)).mul
      (Complex.continuous_ofReal.comp continuous_fst)))
lemma piece_hasDerivAt (p : CardinalData) (ell j : ℕ) (hj : j<6) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t * kernelMoment ell s t)
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * kernelMoment (ell+1) s t) s := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (show ContinuousOn (fun st : ℝ×ℝ => kernelMoment (ell+1) st.1 st.2)
      (Set.Icc (s-1) (s+1) ×ˢ Set.Icc (0:ℝ) 1) from (continuous_joint_kernel _).continuousOn)
  have hr := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s t => density p j t * kernelMoment ell s t)
    (F' := fun s t => density p j t * kernelMoment (ell+1) s t)
    (s := Set.Icc (s-1) (s+1))
    (bound := fun _ => densityBound*(|p.c₀|+|p.d₀|+‖p.x‖)*max C 0)
    (Icc_mem_nhds (by linarith : s-1 < s) (by linarith : s < s+1))
    (Filter.Eventually.of_forall fun x => (intervalIntegrable_iff.mp (piece_integrable p ell j hj x)).aestronglyMeasurable)
    (piece_integrable p ell j hj s)
    (intervalIntegrable_iff.mp (piece_integrable p (ell+1) j hj s)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x hx => by
      rw [norm_mul]
      exact mul_le_mul (density_bound p j (piece_interval_g hj (Set.uIoc_subset_uIcc ht)))
        ((hC (x,t) ⟨hx,piece_interval_g hj (Set.uIoc_subset_uIcc ht)⟩).trans (le_max_left _ _))
        (norm_nonneg _) (by have := densityBound_nonneg; positivity))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => (kernelMoment_hasDerivAt ell t x).const_mul _)
  exact hr.2
lemma K_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (K p ell) (K p (ell+1) s) s := by
  have ha := ((kernelMoment_hasDerivAt ell 0 s).const_mul (Pcoeff 0)).add
    (HasDerivAt.fun_sum (u := Finset.Icc (1:ℕ) 6) fun j _ =>
      (kernelMoment_hasDerivAt ell ((j:ℝ)/6) s).const_mul (2*Pcoeff j))
  have hi := HasDerivAt.fun_sum (u := Finset.range 6) fun j hj =>
    piece_hasDerivAt p ell j (Finset.mem_range.mp hj) s
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((ha.const_mul (p.C:ℂ)).add hi)
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
lemma H₁_hasDerivAt (s : ℝ) :
    HasDerivAt H₁ (cardinalSeries exactData₁ 1 s+K exactData₂ 1 s) s :=
  (cardinal_hasDerivAt exactData₁ s).add (K_hasDerivAt exactData₂ 0 s)
lemma H₂_hasDerivAt (s : ℝ) :
    HasDerivAt H₂ (cardinalSeries exactData₂ 1 s+K exactData₁ 1 s) s :=
  (cardinal_hasDerivAt exactData₂ s).add (K_hasDerivAt exactData₁ 0 s)
lemma exactLists_coordinate (ni : Node×Bool) :
    exactList₁ ni=transformedJets exactData₂ ni-contactList ni ∧
    exactList₂ ni=transformedJets exactData₁ ni := by
  have h1 := congrArg (fun x : X => x ni) exactLists_equations.1
  have h2 := congrArg (fun x : X => x ni) exactLists_equations.2
  simp only [g₁,g₂,lp.coeFn_sub,Pi.sub_apply] at h1 h2
  change exactList₁ ni-S exactList₂ ni=transformedJets (fixed₂ 0) ni-contactList ni at h1
  change exactList₂ ni-S exactList₁ ni=transformedJets (fixed₁ 0) ni at h2
  simp only [exactData₁,exactData₂]
  rw [transformedJets_fixed₁ exactList₁ ni,transformedJets_fixed₂ exactList₂ ni]
  constructor <;> linarith
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
lemma H₁_jets (n : Node) : H₁ n.val=0 ∧ deriv H₁ n.val=if n.val=1 then -Q n.val else 0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).1
  have hd := (exactLists_coordinate (n,true)).1
  simp only [transformedJets,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,contactList_apply,
    and_false,and_true] at hc hd
  have hv := (cardinal_jets exactData₁ n).1
  have hj := (cardinal_jets exactData₁ n).2
  change cardinal exactData₁ n.val=Q n.val*exactList₁ (n,false) at hv
  change deriv (cardinal exactData₁) n.val=
    Q n.val*(exactList₁ (n,true)+D n.val*exactList₁ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₁ _).deriv] at hj
  constructor
  · unfold H₁; rw [hv,hc]; field_simp <;> ring
  · rw [(H₁_hasDerivAt _).deriv,hj,hc,hd]
    split <;> field_simp <;> ring
lemma H₂_jets (n : Node) : H₂ n.val=0 ∧ deriv H₂ n.val=0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).2
  have hd := (exactLists_coordinate (n,true)).2
  simp only [transformedJets,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hc hd
  have hv := (cardinal_jets exactData₂ n).1
  have hj := (cardinal_jets exactData₂ n).2
  change cardinal exactData₂ n.val=Q n.val*exactList₂ (n,false) at hv
  change deriv (cardinal exactData₂) n.val=
    Q n.val*(exactList₂ (n,true)+D n.val*exactList₂ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₂ _).deriv] at hj
  constructor
  · unfold H₂; rw [hv,hc]; field_simp <;> ring
  · rw [(H₂_hasDerivAt _).deriv,hj,hc,hd]
    field_simp <;> ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FourierPairSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

open MeasureTheory ComplexConjugate
open scoped FourierTransform RealInnerProductSpace

open scoped FourierTransform RealInnerProductSpace

namespace SharpPlanar


lemma gaussianCoeff_re (t : ℝ) : (gaussianCoeff t).re = Real.pi*b*h := by
  simp [gaussianCoeff]

lemma gaussianCoeff_re_pos (t : ℝ) : 0 < (gaussianCoeff t).re := by
  rw [gaussianCoeff_re]
  exact mul_pos (mul_pos Real.pi_pos b_pos_g) h_pos_g

lemma spectralGaussian_norm (t : ℝ) (x : Plane) :
    ‖spectralGaussian t x‖ = Real.exp (-Real.pi*b*h*‖x‖^2) := by
  rw [spectralGaussian, Complex.norm_exp]
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, gaussianCoeff_re]
  congr 1
  ring

lemma spectralGaussian_continuous : Continuous (fun q : Plane × ℝ => spectralGaussian q.2 q.1) := by
  unfold spectralGaussian gaussianCoeff
  fun_prop

lemma poisson_gaussian_plane {a : ℂ} (ha : 0 < a.re) (ξ : Plane) :
    𝓕 (fun x : Plane => Complex.exp (-a * (‖x‖ : ℂ)^2)) ξ =
      (Real.pi : ℂ)/a * Complex.exp (-(Real.pi : ℂ)^2 * (‖ξ‖ : ℂ)^2/a) := by
  simpa [Plane, finrank_euclideanSpace_fin] using fourier_gaussian_innerProductSpace ha ξ

lemma gaussianCoeff_ne (t : ℝ) : gaussianCoeff t ≠ 0 := by
  intro he
  have := gaussianCoeff_re_pos t
  simp [he] at this

lemma gaussianCoeff_lambda (t : ℝ) : (Real.pi : ℂ)/gaussianCoeff t = lambda t := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos_g.ne'
  have ht := denominator_ne t
  apply (div_eq_iff (gaussianCoeff_ne t)).mpr
  unfold gaussianCoeff lambda
  field_simp [mul_ne_zero hb ht, ht, hb]
  ring_nf
  simp [Complex.I_sq]

lemma z_lambda_relation (t : ℝ) : Complex.I*z t - h = -lambda t/b := by
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos_g.ne'
  have ht := denominator_ne t
  have hbB : (b : ℂ)^2*(B : ℂ) = 1 := by
    rw [B_eq_inv_b_sq]
    push_cast
    exact mul_inv_cancel₀ (pow_ne_zero 2 hb)
  unfold z lambda
  field_simp [ht, hb, mul_ne_zero hb ht]
  ring_nf
  simp only [Complex.I_sq]
  linear_combination (norm := skip) -Complex.I * hbB
  ring_nf
  simp

lemma gaussianCoeff_exponent (t r : ℝ) :
    -(Real.pi : ℂ)^2 * (r : ℂ)^2 / gaussianCoeff t =
      -(Real.pi : ℂ)*h*(b*r^2) + Complex.I*Real.pi*z t*(b*r^2) := by
  have hlam := gaussianCoeff_lambda t
  have hz := z_lambda_relation t
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast b_pos_g.ne'
  calc
    _ = -(Real.pi : ℂ) * (r : ℂ)^2 * lambda t := by rw [← hlam]; ring
    _ = ((Complex.I*z t - h)*b)*Real.pi*r^2 := by rw [hz]; field_simp
    _ = _ := by ring

lemma spectralGaussian_fourier (t : ℝ) (ξ : Plane) :
    𝓕 (spectralGaussian t) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        kernelMoment 0 (b*‖ξ‖^2) t := by
  change 𝓕 (fun x : Plane => Complex.exp (-gaussianCoeff t * (‖x‖ : ℂ)^2)) ξ = _
  rw [poisson_gaussian_plane (gaussianCoeff_re_pos t), gaussianCoeff_lambda,
    gaussianCoeff_exponent]
  unfold kernelMoment
  simp only [pow_zero, mul_one]
  rw [Complex.ofReal_exp, Complex.exp_add]
  push_cast
  ring

lemma spectralGaussian_integrable (t : ℝ) : Integrable (spectralGaussian t) := by
  convert GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (gaussianCoeff_re_pos t) 0 (0 : Plane) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [spectralGaussian, neg_mul]

lemma gaussian_damping_integrable :
    Integrable (fun x : Plane => Real.exp (-Real.pi*b*h*‖x‖^2)) := by
  simpa only [spectralGaussian_norm] using (spectralGaussian_integrable 0).norm

lemma spectralGaussian_joint_integrable {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    Integrable (fun q : Plane × ℝ =>
      (Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1 * f q.2)
      (volume.prod μ) := by
  have hc : Continuous (fun q : Plane × ℝ =>
      (Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1) := by
    apply Continuous.mul
    · fun_prop
    · exact spectralGaussian_continuous
  apply (gaussian_damping_integrable.mul_prod hf.norm).mono'
    (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)
  apply Filter.Eventually.of_forall
  intro q
  change ‖(Real.fourierChar (-inner ℝ q.1 ξ) : ℂ) * spectralGaussian q.2 q.1 * f q.2‖ ≤ _
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, spectralGaussian_norm]


lemma spectralGaussian_fourier_integral {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    𝓕 (fun x : Plane => ∫ t, spectralGaussian t x * f t ∂μ) ξ =
      ∫ t, 𝓕 (spectralGaussian t) ξ * f t ∂μ := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  simp_rw [← integral_const_mul]
  have hj : Integrable (Function.uncurry (fun x : Plane => fun t : ℝ =>
      (Real.fourierChar (-inner ℝ x ξ) : ℂ) * (spectralGaussian t x * f t)))
      (volume.prod μ) := by
    convert spectralGaussian_joint_integrable hf ξ using 1
    all_goals try with_reducible_and_instances rfl
    ext q
    rcases q with ⟨x, t⟩
    change _ * (_ * _) = _ * _ * _
    ring
  rw [integral_integral_swap hj]
  apply integral_congr_ae
  filter_upwards with t
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with x
  ring

end SharpPlanar

namespace SharpPlanar



lemma fourier_integrable {g : Plane → ℂ} (hg : Integrable g) (ξ : Plane) :
    Integrable (fun x : Plane => (Real.fourierChar (-inner ℝ x ξ) : ℂ) * g x) := by
  simpa only [Circle.smul_def, smul_eq_mul] using
    (Real.fourierIntegral_convergent_iff ξ).mpr hg

lemma fourier_conj_even {g : Plane → ℂ} (he : ∀ x, g (-x) = g x) (ξ : Plane) :
    𝓕 (fun x => conj (g x)) ξ = conj (𝓕 g ξ) := by
  simp only [Real.fourier_eq', smul_eq_mul]
  rw [← integral_conj]
  rw [← integral_neg_eq_self (fun x : Plane =>
    conj (Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_neg_left, he, map_mul]
  congr 1
  simp only [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma complex_re_as_sum (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  apply Complex.ext <;> simp

lemma fourier_integrable_exp {g : Plane → ℂ} (hg : Integrable g) (ξ : Plane) :
    Integrable (fun x : Plane =>
      Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x) := by
  convert fourier_integrable hg ξ using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  congr 1
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring


lemma fourier_re_even {g : Plane → ℂ} (hg : Integrable g)
    (he : ∀ x, g (-x) = g x) (ξ : Plane) :
    𝓕 (fun x => ((g x).re : ℂ)) ξ = ((𝓕 g ξ).re : ℂ) := by
  have hgc : Integrable (fun x => conj (g x)) := by
    exact RCLike.conjCLE.toContinuousLinearMap.integrable_comp hg
  calc
    _ = (𝓕 g ξ + 𝓕 (fun x => conj (g x)) ξ) / 2 := by
      simp only [Real.fourier_eq', smul_eq_mul]
      rw [← integral_add (fourier_integrable_exp hg ξ)
        (fourier_integrable_exp hgc ξ), ← integral_div]
      apply integral_congr_ae
      filter_upwards with x
      rw [complex_re_as_sum]
      ring
    _ = _ := by rw [fourier_conj_even he, ← complex_re_as_sum]

end SharpPlanar

namespace SharpPlanar

lemma gaussianSpectral_integrable {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) : Integrable (gaussianSpectral μ f) := by
  have hi := (spectralGaussian_joint_integrable hf (0 : Plane)).integral_prod_left
  unfold gaussianSpectral
  simpa [Real.fourierChar_apply] using hi

lemma gaussianSpectral_even (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) :
    gaussianSpectral μ f (-x) = gaussianSpectral μ f x := by
  simp [gaussianSpectral, spectralGaussian]

lemma gaussianSpectral_eq (μ : Measure ℝ) (f : ℝ → ℂ) (x : Plane) :
    gaussianSpectral μ f x =
      (Real.exp (-Real.pi*h*(b*‖x‖^2)) : ℂ) * spectral μ f (b*‖x‖^2) := by
  rw [gaussianSpectral, spectral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  unfold spectralGaussian gaussianCoeff
  congr 1
  push_cast
  ring

lemma gaussianSpectral_fourier {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℂ}
    (hf : Integrable f μ) (ξ : Plane) :
    𝓕 (gaussianSpectral μ f) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        ∫ t, kernelMoment 0 (b*‖ξ‖^2) t * f t ∂μ := by
  unfold gaussianSpectral
  rw [spectralGaussian_fourier_integral hf]
  simp_rw [spectralGaussian_fourier, mul_assoc]
  rw [integral_const_mul]

lemma gaussianSpectral_dirac_fourier (t : ℝ) (c : ℂ) (ξ : Plane) :
    𝓕 (gaussianSpectral (Measure.dirac t) (fun _ => c)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) * kernelMoment 0 (b*‖ξ‖^2) t * c := by
  rw [gaussianSpectral_fourier (integrable_dirac (by finiteness)), integral_dirac]
  ring

lemma density_piece_integrable (p : CardinalData) {j : ℕ} (hj : j < 6) :
    IntegrableOn (density p j) (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply (continuousOn_density_g p j).mono
  intro t ht
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast (Nat.le_of_lt_succ hj)
  have hj0 : (0 : ℝ) ≤ j := by positivity
  constructor <;> linarith [ht.1, ht.2]

lemma fourier_add_integrable {f g : Plane → ℂ} (hf : Integrable f)
    (hg : Integrable g) (ξ : Plane) :
    𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  simp only [Real.fourier_eq', smul_eq_mul, mul_add]
  rw [integral_add (fourier_integrable_exp hf ξ) (fourier_integrable_exp hg ξ)]

lemma fourier_sum_integrable {ι : Type*} (s : Finset ι) (f : ι → Plane → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : Plane) :
    𝓕 (fun x => ∑ i ∈ s, f i x) ξ = ∑ i ∈ s, 𝓕 (f i) ξ := by
  classical
  simp only [Real.fourier_eq', smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi => fourier_integrable_exp (hf i hi) ξ)]

lemma qComplex_integrable (p : CardinalData) : Integrable (qComplex p) := by
  apply Integrable.add
  · apply Integrable.add
    · exact gaussianSpectral_integrable (integrable_dirac (by finiteness))
    · exact integrable_finsetSum _ fun j _ =>
        gaussianSpectral_integrable (integrable_dirac (by finiteness))
  · exact integrable_finsetSum _ fun j hj =>
      gaussianSpectral_integrable (density_piece_integrable p (Finset.mem_range.mp hj))

lemma qComplex_even (p : CardinalData) (x : Plane) : qComplex p (-x) = qComplex p x := by
  simp only [qComplex, gaussianSpectral_even]

lemma qComplex_re (p : CardinalData) (x : Plane) : (qComplex p x).re = qSchwartz p x := by
  rw [qSchwartz_apply]
  simp only [qComplex, gaussianSpectral_eq, ← Finset.mul_sum, ← mul_add]
  simp only [cardinal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

lemma qComplex_fourier (p : CardinalData) (ξ : Plane) :
    (𝓕 (qComplex p) ξ).re =
      Real.exp (-Real.pi*h*(b*‖ξ‖^2)) * K p 0 (b*‖ξ‖^2) := by
  have h₀ : Integrable (gaussianSpectral (Measure.dirac 0)
      (fun _ => (p.C : ℂ)*Pcoeff 0)) :=
    gaussianSpectral_integrable (integrable_dirac (by finiteness))
  have h₁ : ∀ j ∈ Finset.Icc (1 : ℕ) 6,
      Integrable (gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j)) := fun _ _ =>
    gaussianSpectral_integrable (integrable_dirac (by finiteness))
  have h₂ : ∀ j ∈ Finset.range 6,
      Integrable (gaussianSpectral (volume.restrict
        (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6))) (density p j)) := fun j hj =>
    gaussianSpectral_integrable (density_piece_integrable p (Finset.mem_range.mp hj))
  unfold qComplex
  have h01 : Integrable (fun x =>
      gaussianSpectral (Measure.dirac 0) (fun _ => (p.C : ℂ)*Pcoeff 0) x +
      ∑ j ∈ Finset.Icc (1 : ℕ) 6, gaussianSpectral (Measure.dirac ((j : ℝ)/6))
        (fun _ => 2*(p.C : ℂ)*Pcoeff j) x) := h₀.add (integrable_finsetSum _ h₁)
  rw [fourier_add_integrable h01
      (integrable_finsetSum _ h₂),
    fourier_add_integrable h₀ (integrable_finsetSum _ h₁),
    fourier_sum_integrable _ _ h₁, fourier_sum_integrable _ _ h₂]
  simp_rw [gaussianSpectral_dirac_fourier]
  have hd : ∀ j ∈ Finset.range 6,
      𝓕 (gaussianSpectral (volume.restrict
        (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6))) (density p j)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) : ℂ) *
        ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
          density p j t * kernelMoment 0 (b*‖ξ‖^2) t := by
    intro j hj
    rw [gaussianSpectral_fourier (density_piece_integrable p (Finset.mem_range.mp hj)),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    exact mul_comm _ _
  rw [Finset.sum_congr rfl hd]
  simp only [mul_assoc, ← Finset.mul_sum, ← mul_add]
  have ha : kernelMoment 0 (b*‖ξ‖^2) 0 * ((p.C : ℂ)*Pcoeff 0) +
      (∑ j ∈ Finset.Icc (1 : ℕ) 6,
        kernelMoment 0 (b*‖ξ‖^2) ((j : ℝ)/6) * (2*((p.C : ℂ)*Pcoeff j))) =
      (p.C : ℂ) * (Pcoeff 0 * kernelMoment 0 (b*‖ξ‖^2) 0 +
        ∑ j ∈ Finset.Icc (1 : ℕ) 6,
          2 * Pcoeff j * kernelMoment 0 (b*‖ξ‖^2) ((j : ℝ)/6)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  rw [ha]
  simp only [K, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma qSchwartz_fourier (p : CardinalData) (ξ : Plane) :
    𝓕 (fun x : Plane => (qSchwartz p x : ℂ)) ξ =
      (Real.exp (-Real.pi*h*(b*‖ξ‖^2)) * K p 0 (b*‖ξ‖^2) : ℝ) := by
  simp_rw [← qComplex_re]
  rw [fourier_re_even (qComplex_integrable p) (qComplex_even p), qComplex_fourier]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
lemma kSchwartz_apply (p : CardinalData) (x : Plane) :
    kSchwartz p x=Real.exp (-Real.pi*h*(b*‖x‖^2))*K p 0 (b*‖x‖^2) := by
  change (𝓕 (qComplexSchwartz p) x).re=_
  rw [SchwartzMap.fourier_coe]
  change (𝓕 (fun x : Plane => (qSchwartz p x:ℂ)) x).re=_
  rw [qSchwartz_fourier]
  rfl
lemma pairLeft_apply (p q : CardinalData) (x : Plane) :
    pairLeft p q x=Real.exp (-Real.pi*h*(b*‖x‖^2))*(cardinal p (b*‖x‖^2)+K q 0 (b*‖x‖^2)) := by
  change qSchwartz p x+kSchwartz q x=_
  rw [qSchwartz_apply,kSchwartz_apply,mul_add]
lemma pairRight_apply (p q : CardinalData) (x : Plane) :
    pairRight p q x=Real.exp (-Real.pi*h*(b*‖x‖^2))*(cardinal q (b*‖x‖^2)+K p 0 (b*‖x‖^2)) :=
  pairLeft_apply q p x
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
-- module Solutions.OAIQ098_PP.Triangular_Energy_Theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace TriangularUniversal.Theta

lemma intGaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-a * (n : ℝ)^2)) := by
  have h := (isLittleO_exp_neg_mul_sq_cocompact
    (show 0 < (a : ℂ).re from ha) (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite
  have H : Summable (fun n : ℤ => Complex.exp (-(a : ℂ) * (n : ℂ)^2)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      (by simpa only [Function.comp_def, Complex.ofReal_intCast] using h)
  simpa [Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im] using H.norm

end TriangularUniversal.Theta

end

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_GaussianSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
open Complex

lemma gaussian_shift_poisson {a : ℂ} (ha : 0 < a.re) (d : ℝ) :
    (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)*a*((n:ℂ)+d)^2)) =
      1/a^(1/2:ℂ) * ∑' n : ℤ,
        Complex.exp (-(Real.pi:ℂ)/a*(n:ℂ)^2+2*(Real.pi:ℂ)*Complex.I*n*d) := by
  have hane : a≠0 := by intro h; simp [h] at ha
  have hh := Complex.tsum_exp_neg_quadratic ha (-a*d)
  have hleft (n : ℤ) :
      Complex.exp (-(Real.pi:ℂ)*a*((n:ℂ)+d)^2) =
        Complex.exp (-(Real.pi:ℂ)*a*d^2) *
          Complex.exp (-(Real.pi:ℂ)*a*(n:ℂ)^2+2*(Real.pi:ℂ)*(-a*d)*n) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [hleft]
  rw [tsum_mul_left,hh]
  calc
    _ = 1/a^(1/2:ℂ) * (Complex.exp (-(Real.pi:ℂ)*a*d^2) *
        ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)/a*((n:ℂ)+Complex.I*(-a*d))^2)) := by ring
    _ = _ := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [← Complex.exp_add]
      congr 1
      field_simp
      ring_nf
      simp [Complex.I_sq]

lemma real_integer_gaussian_summable {a : ℝ} (ha : 0<a) :
    Summable (fun n : ℤ => Real.exp (-a*(n:ℝ)^2)) :=
  TriangularUniversal.Theta.intGaussian_summable ha

lemma gaussian_scale_half_product {a : ℂ} (ha : a≠0) {r : ℝ} (hr : 0 < r) :
    (a/(r:ℂ))^(1/2:ℂ)*(a*r)^(1/2:ℂ)=a := by
  have hrn : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (div_ne_zero ha hrn),
    Complex.cpow_def_of_ne_zero (mul_ne_zero ha hrn)]
  rw [← Complex.exp_add]
  have hh : Complex.log (a/(r:ℂ))=(Complex.log a)-(Real.log r:ℂ) := by
    rw [div_eq_mul_inv,← Complex.ofReal_inv,Complex.log_mul_ofReal r⁻¹ (inv_pos.mpr hr) a ha,
      Real.log_inv,Complex.ofReal_neg]
    ring
  rw [hh,Complex.log_mul_ofReal r hr a ha]
  convert Complex.exp_log ha using 2 <;> first | rfl | ring

lemma phase_gaussian_summable {A B : ℂ} (hA : 0<A.re) (hB : 0<B.re) (c : ℝ) :
    Summable (fun p : ℤ×ℤ => Complex.exp (-A*(p.1:ℂ)^2-B*(p.2:ℂ)^2+
      (c:ℂ)*Complex.I*p.1*p.2)) := by
  apply Summable.of_norm
  have hh := (real_integer_gaussian_summable hA).mul_of_nonneg
    (real_integer_gaussian_summable hB) (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [Complex.norm_exp,← Real.exp_add]
  congr 1
  simp only [← Complex.ofReal_intCast,← Complex.ofReal_pow,
    Complex.add_re,Complex.sub_re,Complex.neg_re,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma hexForm_nonneg (v : ℤ×ℤ) : 0 ≤ hexForm v := by
  unfold hexForm
  nlinarith [sq_nonneg (2*v.1+v.2),sq_nonneg v.2]
lemma hexNat_coe (v : ℤ×ℤ) : (hexNat v:ℤ)=hexForm v := Int.toNat_of_nonneg (hexForm_nonneg v)
lemma hexPoint_radius (v : ℤ×ℤ) : b*‖hexPoint v‖^2=(hexNat v:ℝ) := by
  have hb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr b_pos_g).ne'
  have hs := Real.sq_sqrt b_pos_g.le
  have hn : (hexNat v:ℝ)=(v.1:ℝ)^2+(v.1:ℝ)*(v.2:ℝ)+(v.2:ℝ)^2 := by
    exact_mod_cast hexNat_coe v
  rw [hn,EuclideanSpace.norm_sq_eq]
  simp only [hexPoint,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    PiLp.toLp_apply,Real.norm_eq_abs,sq_abs]
  rw [div_pow,mul_pow,hs]
  field_simp [b_pos_g.ne']
  nlinarith [b_sq_g]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Complex
lemma theta_first {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0 < r) (k : ℤ) :
    (∑' j : ℤ, thetaKernel a r k j) =
      1/(a/(r:ℂ))^(1/2:ℂ) * ∑' m : ℤ,
        Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k) := by
  have hA : 0<(a/(r:ℂ)).re := by
    rw [Complex.div_ofReal_re]; exact div_pos ha hr
  have hh := gaussian_shift_poisson hA ((k:ℝ)/2)
  have he (j : ℤ) : thetaKernel a r k j =
      Complex.exp (-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2)*
        Complex.exp (-(Real.pi:ℂ)*(a/(r:ℂ))*((j:ℂ)+(k:ℂ)/2)^2) := by
    rw [thetaKernel,← Complex.exp_add]; congr 1; ring
  simp_rw [he]
  rw [tsum_mul_left]
  push_cast at hh
  rw [hh]
  calc
    _ = 1/(a/(r:ℂ))^(1/2:ℂ) * (Complex.exp (-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2)*
        ∑' m : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2+
          2*(Real.pi:ℂ)*Complex.I*m*((k:ℂ)/2))) := by ring
    _ = _ := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr; intro m
      rw [← Complex.exp_add]; congr 1; ring
lemma theta_second {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0 < r) (m : ℤ) :
    (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k)) =
      1/(a*r)^(1/2:ℂ) * ∑' n : ℤ, thetaKernel (1/a) r (-m) n := by
  have hB : 0<(a*(r:ℂ)).re := by
    rw [Complex.mul_re]; simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_pos ha hr
  have an : a≠0 := by intro h; simp [h] at ha
  have rn : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  have hh := Complex.tsum_exp_neg_quadratic hB (Complex.I*(m:ℂ)/2)
  have he (k : ℤ) :
      Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k) =
      Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2)*
        Complex.exp (-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2+
          2*(Real.pi:ℂ)*(Complex.I*(m:ℂ)/2)*k) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [he]
  rw [tsum_mul_left,hh]
  calc
    _ = 1/(a*r)^(1/2:ℂ) * (Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2)*
        ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)/(a*r)*((n:ℂ)+Complex.I*(Complex.I*(m:ℂ)/2))^2)) := by ring
    _ = _ := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr; intro n
      rw [thetaKernel,← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring_nf
      simp [Complex.I_sq]
lemma thetaKernel_norm (a : ℂ) (r : ℝ) (k j : ℤ) :
    ‖thetaKernel a r k j‖ = Real.exp (-Real.pi*a.re*((j+(k:ℝ)/2)^2/r+r*(k:ℝ)^2)) := by
  rw [thetaKernel,Complex.norm_exp]
  congr 1
  simp only [← Complex.ofReal_intCast,← Complex.ofReal_pow,← Complex.ofReal_add,
    ← Complex.ofReal_mul,← Complex.ofReal_div,← Complex.ofReal_ofNat,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,mul_zero,zero_mul,sub_zero,neg_zero]

lemma theta_quadratic_bound {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    min (1/r) r/2*(x^2+y^2) ≤ (x+y/2)^2/r+r*y^2 := by
  have hm : 0 ≤ min (1/r) r := (lt_min (one_div_pos.mpr hr) hr).le
  calc
    _ ≤ min (1/r) r*((x+y/2)^2+y^2) := by
      have hh : (x^2+y^2)/2 ≤ (x+y/2)^2+y^2 := by
        nlinarith [sq_nonneg (x+y),sq_nonneg y]
      nlinarith [mul_le_mul_of_nonneg_left hh hm]
    _ ≤ _ := by
      simp only [mul_add,div_eq_mul_inv,one_mul]
      exact add_le_add
        (by nlinarith [mul_le_mul_of_nonneg_right (min_le_left r⁻¹ r) (sq_nonneg (x+y/2))])
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg y))

lemma thetaKernel_summable {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0 < r) :
    Summable (fun p : ℤ×ℤ => thetaKernel a r p.1 p.2) := by
  let c : ℝ := Real.pi*a.re*(min (1/r) r/2)
  have hc : 0 < c := by dsimp [c]; exact mul_pos (mul_pos Real.pi_pos ha) (div_pos (lt_min (one_div_pos.mpr hr) hr) (by norm_num))
  have hh := (real_integer_gaussian_summable hc).mul_of_nonneg
    (real_integer_gaussian_summable hc) (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  apply Summable.of_norm_bounded hh
  intro p
  rw [thetaKernel_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht := theta_quadratic_bound hr (p.2:ℝ) (p.1:ℝ)
  dsimp [c]
  nlinarith [mul_le_mul_of_nonneg_left ht (mul_pos Real.pi_pos ha).le]

lemma theta_poisson {a : ℂ} (ha : 0<a.re) {r : ℝ} (hr : 0 < r) :
    (∑' p : ℤ×ℤ, thetaKernel a r p.1 p.2) =
      1/a * ∑' p : ℤ×ℤ, thetaKernel (1/a) r p.1 p.2 := by
  have an : a≠0 := by intro h; simp [h] at ha
  have hA : 0<(a/(r:ℂ)).re := by rw [Complex.div_ofReal_re]; exact div_pos ha hr
  have hAn : a/(r:ℂ)≠0 := by intro h; simp [h] at hA
  have hAi : 0<((Real.pi:ℂ)/(a/(r:ℂ))).re := by
    rw [div_eq_mul_inv,Complex.mul_re,Complex.inv_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos Real.pi_pos (div_pos hA (Complex.normSq_pos.mpr hAn))
  have hB : 0<((Real.pi:ℂ)*(a*r)).re := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero]
    exact mul_pos Real.pi_pos (mul_pos ha hr)
  have hmid := phase_gaussian_summable hAi hB Real.pi
  have hi : 0<(1/a).re := by
    rw [one_div,Complex.inv_re]; exact div_pos ha (Complex.normSq_pos.mpr an)
  rw [(thetaKernel_summable ha hr).tsum_prod,(thetaKernel_summable hi hr).tsum_prod]
  simp_rw [theta_first ha hr]
  rw [tsum_mul_left]
  have hswap :
      (∑' k : ℤ, ∑' m : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k)) =
      ∑' m : ℤ, ∑' k : ℤ, Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-
          (Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k) := by
    exact (show Summable (Function.uncurry fun (m k : ℤ) => Complex.exp (-(Real.pi:ℂ)/(a/(r:ℂ))*(m:ℂ)^2-(Real.pi:ℂ)*(a*r)*(k:ℂ)^2+(Real.pi:ℂ)*Complex.I*m*k)) by
      convert hmid using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      simp only [Function.uncurry]
      ring_nf).tsum_comm
  rw [hswap]
  simp_rw [theta_second ha hr]
  rw [tsum_mul_left,← mul_assoc,one_div_mul_one_div,
    gaussian_scale_half_product an hr]
  congr 1
  exact (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ∑' j : ℤ, thetaKernel (1/a) r k j)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticeGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
lemma latticePoint_zero : latticePoint 0=0 := by
  ext i
  fin_cases i <;> simp [latticePoint,hexPoint]
lemma latticePoint_norm (p : ℤ×ℤ) :
    ‖latticePoint p‖^2=((p.2:ℝ)+(p.1:ℝ)/2)^2/b+b*(p.1:ℝ)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [latticePoint,hexPoint,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    PiLp.toLp_apply,Real.norm_eq_abs,sq_abs]
  rw [div_pow,mul_pow,Real.sq_sqrt b_pos_g.le]
lemma thetaKernel_lattice (a : ℂ) (p : ℤ×ℤ) :
    thetaKernel a b p.1 p.2=Complex.exp (-(Real.pi:ℂ)*a*(‖latticePoint p‖:ℂ)^2) := by
  rw [thetaKernel]
  congr 1
  have hh : ((p.2:ℂ)+(p.1:ℂ)/2)^2/(b:ℂ)+(b:ℂ)*(p.1:ℂ)^2=(‖latticePoint p‖:ℂ)^2 := by
    exact_mod_cast (latticePoint_norm p).symm
  rw [hh]
lemma spectralParameter_re (t : ℝ) : (spectralParameter t).re=b*h := by
  simp [spectralParameter]
lemma spectralParameter_pos (t : ℝ) : 0<(spectralParameter t).re := by
  rw [spectralParameter_re]; exact mul_pos b_pos_g h_pos_g
lemma gaussianCoeff_parameter (t : ℝ) : gaussianCoeff t=(Real.pi:ℂ)*spectralParameter t := by
  unfold gaussianCoeff spectralParameter
  ring
lemma spectralGaussian_lattice (t : ℝ) (p : ℤ×ℤ) :
    spectralGaussian t (latticePoint p)=thetaKernel (spectralParameter t) b p.1 p.2 := by
  rw [thetaKernel_lattice,spectralGaussian,gaussianCoeff_parameter]
  congr 1; ring
lemma spectralGaussian_fourier_lattice (t : ℝ) (p : ℤ×ℤ) :
    𝓕 (spectralGaussian t) (latticePoint p)=
    1/spectralParameter t*thetaKernel (1/spectralParameter t) b p.1 p.2 := by
  rw [thetaKernel_lattice]
  change 𝓕 (fun x : Plane => Complex.exp (-gaussianCoeff t*(‖x‖:ℂ)^2)) (latticePoint p)=_
  rw [poisson_gaussian_plane (gaussianCoeff_re_pos t),gaussianCoeff_parameter]
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have he : (Real.pi:ℂ)/((Real.pi:ℂ)*spectralParameter t)=1/spectralParameter t := by field_simp
  rw [he]
  congr 2
  field_simp
lemma spectralGaussian_hex_poisson (t : ℝ) :
    (∑' p : ℤ×ℤ, spectralGaussian t (latticePoint p)) =
      ∑' p : ℤ×ℤ, 𝓕 (spectralGaussian t) (latticePoint p) := by
  simp_rw [spectralGaussian_lattice,spectralGaussian_fourier_lattice]
  rw [tsum_mul_left,theta_poisson (spectralParameter_pos t) b_pos_g]
lemma latticeDamping_nonneg (p : ℤ×ℤ) : 0≤latticeDamping p := (Real.exp_pos _).le
lemma latticeDamping_summable : Summable latticeDamping := by
  change Summable (fun p : ℤ×ℤ => Real.exp (-Real.pi*b*h*‖latticePoint p‖^2))
  have hh: Summable (fun p : ℤ×ℤ => thetaKernel (spectralParameter 0) b p.1 p.2) :=
    thetaKernel_summable (spectralParameter_pos 0) b_pos_g
  have hn:=hh.norm
  simpa only [← spectralGaussian_lattice,spectralGaussian_norm,latticeDamping] using hn
lemma lattice_spectral_bound (t : ℝ) (p : ℤ×ℤ) :
    ‖spectralGaussian t (latticePoint p)‖=latticeDamping p := spectralGaussian_norm t _
lemma lattice_fourier_spectral_bound {t : ℝ} (ht : |t|≤1) (p : ℤ×ℤ) :
    ‖𝓕 (spectralGaussian t) (latticePoint p)‖≤1/(b*h)*latticeDamping p := by
  rw [spectralGaussian_fourier,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hs : 0≤b*‖latticePoint p‖^2 := mul_nonneg b_pos_g.le (sq_nonneg _)
  have hh:=kernelMoment_bound 0 hs ht
  norm_num only [pow_zero,mul_one] at hh
  have he : Real.exp (-kappa*(b*‖latticePoint p‖^2))≤1 := by
    rw [Real.exp_le_one_iff]; simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg kappa_pos.le hs)
  have hu: ‖kernelMoment 0 (b*‖latticePoint p‖^2) t‖≤1/(b*h) :=
    hh.trans (by nlinarith [mul_nonneg (one_div_pos.mpr (mul_pos b_pos_g h_pos_g)).le (sub_nonneg.mpr he)])
  have heq : Real.exp (-Real.pi*h*(b*‖latticePoint p‖^2))=latticeDamping p := by
    unfold latticeDamping; congr 1; ring
  rw [heq,mul_comm]
  exact mul_le_mul_of_nonneg_right hu (latticeDamping_nonneg p)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticeIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
lemma lattice_integral_hasSum {μ : Measure ℝ} {f : ℝ→ℂ} (hf : Integrable f μ)
    {K : (ℤ×ℤ)→ℝ→ℂ} (hK : ∀ p, AEStronglyMeasurable (K p) μ)
    {C : (ℤ×ℤ)→ℝ} (hC : Summable C)
    (hb : ∀ᵐ t ∂μ, ∀ p, ‖K p t‖≤C p) :
    HasSum (fun p => ∫ t, K p t*f t ∂μ)
      (∫ t, (∑' p, K p t)*f t ∂μ) := by
  apply hasSum_integral_of_dominated_convergence (fun p t => C p*‖f t‖)
  · intro p; exact (hK p).mul hf.aestronglyMeasurable
  · intro p
    filter_upwards [hb] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ht p) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun t => hC.mul_right ‖f t‖
  · simpa only [tsum_mul_right] using hf.norm.const_mul (∑' p, C p)
  · filter_upwards [hb] with t ht
    have hs : Summable (fun p => K p t) := Summable.of_norm_bounded hC (ht)
    exact hs.hasSum.mul_right (f t)
lemma lattice_direct_hasSum {μ : Measure ℝ} {f : ℝ→ℂ} (hf : Integrable f μ) :
    HasSum (fun p : ℤ×ℤ => gaussianSpectral μ f (latticePoint p))
      (∫ t, (∑' p : ℤ×ℤ, spectralGaussian t (latticePoint p))*f t ∂μ) := by
  apply lattice_integral_hasSum hf
    (fun p => ((spectralGaussian_continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
    latticeDamping_summable
  exact Filter.Eventually.of_forall fun t p => (lattice_spectral_bound t p).le
lemma lattice_transform_hasSum {μ : Measure ℝ} [SFinite μ] {f : ℝ→ℂ}
    (hf : Integrable f μ) (ht : ∀ᵐ t ∂μ, |t|≤1) :
    HasSum (fun p : ℤ×ℤ => 𝓕 (gaussianSpectral μ f) (latticePoint p))
      (∫ t, (∑' p : ℤ×ℤ, 𝓕 (spectralGaussian t) (latticePoint p))*f t ∂μ) := by
  have hm (p : ℤ×ℤ) : AEStronglyMeasurable (fun t : ℝ => 𝓕 (spectralGaussian t) (latticePoint p)) μ := by
    simp_rw [spectralGaussian_fourier]
    exact (continuous_const.mul (continuous_kernelMoment 0 _)).aestronglyMeasurable
  have hh := lattice_integral_hasSum hf hm
    (latticeDamping_summable.mul_left (1/(b*h)))
    (ht.mono fun t ht p => lattice_fourier_spectral_bound ht p)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact spectralGaussian_fourier_integral hf (latticePoint p)
lemma gaussianSpectral_hex_poisson {μ : Measure ℝ} [SFinite μ] {f : ℝ→ℂ}
    (hf : Integrable f μ) (ht : ∀ᵐ t ∂μ, |t|≤1) :
    (∑' p : ℤ×ℤ, gaussianSpectral μ f (latticePoint p)) =
      ∑' p : ℤ×ℤ, 𝓕 (gaussianSpectral μ f) (latticePoint p) := by
  rw [(lattice_direct_hasSum hf).tsum_eq,(lattice_transform_hasSum hf ht).tsum_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => congrArg (fun z : ℂ => z*f t) (spectralGaussian_hex_poisson t)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
lemma HasLatticePoisson.add {f g : Plane→ℂ} (hf : HasLatticePoisson f)
    (hg : HasLatticePoisson g) : HasLatticePoisson (fun x => f x+g x) where
  integrable := hf.integrable.add hg.integrable
  summable := hf.summable.add hg.summable
  fourier_summable := by
    simp_rw [fourier_add_integrable hf.integrable hg.integrable]
    exact hf.fourier_summable.add hg.fourier_summable
  eq := by
    simp_rw [fourier_add_integrable hf.integrable hg.integrable]
    rw [hf.summable.tsum_add hg.summable,hf.fourier_summable.tsum_add hg.fourier_summable,
      hf.eq,hg.eq]
lemma HasLatticePoisson.zero : HasLatticePoisson (fun _ : Plane => (0 : ℂ)) where
  integrable := integrable_zero _ _ _
  summable := summable_zero
  fourier_summable := by
    simp only [Real.fourier_eq',smul_zero,integral_zero]
    exact summable_zero
  eq := by simp [Real.fourier_eq']
lemma HasLatticePoisson.finset_sum {ι : Type*} (s : Finset ι) (f : ι→Plane→ℂ)
    (hf : ∀ j∈s, HasLatticePoisson (f j)) :
    HasLatticePoisson (fun x => ∑ j∈s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasLatticePoisson.zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
lemma gaussianSpectral_hasPoisson {μ : Measure ℝ} [SFinite μ] {f : ℝ→ℂ}
    (hf : Integrable f μ) (ht : ∀ᵐ t ∂μ, |t|≤1) : HasLatticePoisson (gaussianSpectral μ f) where
  integrable := gaussianSpectral_integrable hf
  summable := (lattice_direct_hasSum hf).summable
  fourier_summable := (lattice_transform_hasSum hf ht).summable
  eq := gaussianSpectral_hex_poisson hf ht
lemma gaussianSpectral_dirac_hasPoisson {t : ℝ} (ht : |t|≤1) (c : ℂ) :
    HasLatticePoisson (gaussianSpectral (Measure.dirac t) (fun _ => c)) := by
  apply gaussianSpectral_hasPoisson (integrable_dirac (by finiteness))
  simpa only [ae_dirac_eq,Filter.eventually_pure] using ht
lemma density_piece_hasPoisson (p : CardinalData) {j : ℕ} (hj : j<6) :
    HasLatticePoisson (gaussianSpectral
      (volume.restrict (Set.Icc ((j:ℝ)/6) (((j:ℝ)+1)/6))) (density p j)) := by
  apply gaussianSpectral_hasPoisson (density_piece_integrable p hj)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hj' : (j:ℝ)≤5 := by exact_mod_cast Nat.le_of_lt_succ hj
  have h0 : 0≤(j:ℝ) := Nat.cast_nonneg _
  have ht0 : 0≤t := by linarith [ht.1]
  rw [abs_of_nonneg ht0]
  linarith [ht.2]
lemma qComplex_hasPoisson (p : CardinalData) : HasLatticePoisson (qComplex p) := by
  apply HasLatticePoisson.add
  · apply HasLatticePoisson.add
    · apply gaussianSpectral_dirac_hasPoisson
      norm_num
    · apply HasLatticePoisson.finset_sum
      intro j hj
      apply gaussianSpectral_dirac_hasPoisson
      rw [abs_of_nonneg (by positivity)]
      have hj' : (j:ℝ)≤6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
      linarith
  · apply HasLatticePoisson.finset_sum
    intro j hj
    exact density_piece_hasPoisson p (Finset.mem_range.mp hj)
lemma qk_lattice_summable (p : CardinalData) :
    Summable (fun n : ℤ×ℤ => qSchwartz p (latticePoint n)) ∧
    Summable (fun n : ℤ×ℤ => kSchwartz p (latticePoint n)) := by
  constructor
  · simpa only [Function.comp_def,Complex.reCLM_apply,qComplex_re] using
      (qComplex_hasPoisson p).summable.mapL Complex.reCLM
  · have hh := (qComplex_hasPoisson p).fourier_summable.mapL Complex.reCLM
    simpa only [Function.comp_def,Complex.reCLM_apply,qComplex_fourier,← kSchwartz_apply] using hh
lemma qk_lattice_poisson (p : CardinalData) :
    (∑' n : ℤ×ℤ, qSchwartz p (latticePoint n))=
      ∑' n : ℤ×ℤ, kSchwartz p (latticePoint n) := by
  have hh := congrArg Complex.re (qComplex_hasPoisson p).eq
  rw [Complex.re_tsum (qComplex_hasPoisson p).summable,
    Complex.re_tsum (qComplex_hasPoisson p).fourier_summable] at hh
  simpa only [qComplex_re,qComplex_fourier,← kSchwartz_apply] using hh
lemma pair_lattice_poisson (p q : CardinalData) :
    (∑' n : ℤ×ℤ, pairLeft p q (latticePoint n))=
      ∑' n : ℤ×ℤ, pairRight p q (latticePoint n) := by
  change (∑' n : ℤ×ℤ, (qSchwartz p (latticePoint n)+kSchwartz q (latticePoint n)))=
    ∑' n : ℤ×ℤ, (qSchwartz q (latticePoint n)+kSchwartz p (latticePoint n))
  rw [(qk_lattice_summable p).1.tsum_add (qk_lattice_summable q).2,
    (qk_lattice_summable q).1.tsum_add (qk_lattice_summable p).2,
    qk_lattice_poisson p,qk_lattice_poisson q,add_comm]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_OriginIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality at the origin from triangular lattice contacts and Poisson summation -/

namespace SharpPlanar
lemma exactLeft_apply (x : Plane) : exactLeft x=Real.exp (-Real.pi*h*(b*‖x‖^2))*H₁ (b*‖x‖^2) :=
  pairLeft_apply _ _ _
lemma exactRight_apply (x : Plane) : exactRight x=Real.exp (-Real.pi*h*(b*‖x‖^2))*H₂ (b*‖x‖^2) :=
  pairRight_apply _ _ _
lemma nonzero_swap {p : ℤ×ℤ} (hp : p≠0) : (p.2,p.1)≠0 := by
  intro hh
  apply hp
  exact Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh)
lemma exactLeft_lattice_zero {p : ℤ×ℤ} (hp : p≠0) : exactLeft (latticePoint p)=0 := by
  rw [exactLeft_apply]
  change Real.exp _*H₁ (b*‖hexPoint (p.2,p.1)‖^2)=_
  rw [hexPoint_radius]
  have hh: H₁ (hexNat (p.2,p.1):ℝ)=0 := (H₁_jets (hexNode (p.2,p.1) (nonzero_swap hp))).1
  rw [hh,mul_zero]
lemma exactRight_lattice_zero {p : ℤ×ℤ} (hp : p≠0) : exactRight (latticePoint p)=0 := by
  rw [exactRight_apply]
  change Real.exp _*H₂ (b*‖hexPoint (p.2,p.1)‖^2)=_
  rw [hexPoint_radius]
  have hh: H₂ (hexNat (p.2,p.1):ℝ)=0 := (H₂_jets (hexNode (p.2,p.1) (nonzero_swap hp))).1
  rw [hh,mul_zero]
lemma exact_origin_identity : exactLeft 0=exactRight 0 := by
  have hh:=pair_lattice_poisson exactData₁ exactData₂
  change (∑' p : ℤ×ℤ, exactLeft (latticePoint p))=(∑' p : ℤ×ℤ, exactRight (latticePoint p)) at hh
  rw [tsum_eq_single (0 : ℤ×ℤ) (fun p hp => exactLeft_lattice_zero hp),
    tsum_eq_single (0 : ℤ×ℤ) (fun p hp => exactRight_lattice_zero hp),latticePoint_zero] at hh
  exact hh
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_OriginPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positivity at the origin of the exact Fourier pair -/

namespace SharpPlanar
open IntegerIntervals CachedData
lemma exactJet_zero_H₂ (s : ℝ) : exactJet true 0 s=H₂ s := by
  simp only [exactJet,exactData,ite_true, if_true,Bool.not_true,Bool.false_eq_true,ite_false, if_false,← cardinal_eq_cardinalSeries,H₂]
lemma tableOrigin_lower : (3:ℝ)<tableHJet true 0 0 := by
  have hh := RBox.contains_add_g hm0_1_0_0.realContains_g hm0_0_1_0.realContains
  have hl := @RBox.lower_lt_g _ _ 3 1 hh (by norm_num) (by decide +kernel)
  simpa only [fullMoment_direct_g,fullMoment_transformed,Nat.factorial_zero,Nat.cast_one,div_one,one_div,tableHJet,Bool.not_true,Int.cast_ofNat,Int.cast_one,div_one] using hl
lemma exactRight_origin_positive : 0<exactRight 0 := by
  have he:=error_zero_cap_g true (show (0:ℝ)≤0 by norm_num)
  have hl:=tableOrigin_lower
  have hh:= (abs_lt.mp he).1
  rw [exactJet_zero_H₂] at hh
  rw [exactRight_apply]
  norm_num only [norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,Real.exp_zero,one_mul]
  linarith
lemma exactLeft_origin_positive_g_oai : 0<exactLeft 0 := by rw [exact_origin_identity]; exact exactRight_origin_positive
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.exactLeft_origin_positive_g_oai := @OAI.SharpPlanar.exactLeft_origin_positive_g_oai
