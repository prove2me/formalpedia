-- Prove2me | solution 1 for OAI.SharpPlanar.Scoords_mem_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:09:15.955281+00:00
-- url     : https://prove2.me/submissions/dca31533-8eb5-4489-9a08-963487389c11

import Mathlib
import Definitions.Def_OAIQ098E002
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_Pcoeff_norm_e
import Theorems.Thm_OAI_SharpPlanar_X_norm_e
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_e
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_h_pos_e
import Theorems.Thm_OAI_SharpPlanar_piece_interval_e
import Theorems.Thm_OAI_SharpPlanar_positive_coeff_mass_e
import Theorems.Thm_OAI_SharpPlanar_summand_bound_e
import Theorems.Thm_OAI_SharpPlanar_u_bound_e
import Theorems.Thm_OAI_SharpPlanar_v_bound_e

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
  simpa [abs_of_pos h_pos_e] using hh

theorem lambda_bound (t : ℝ) : ‖lambda t‖ ≤ 1 / (b * h) := by
  rw [lambda, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos b_pos_e]
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos b_pos_e h_pos_e)
  exact mul_le_mul_of_nonneg_left (imaginary_gaussian_denominator t) b_pos_e.le

theorem z_bound (t : ℝ) : ‖z t‖ ≤ B / h + h := by
  have hden : 0 < ‖(t : ℂ) + Complex.I * (h : ℂ)‖ :=
    h_pos_e.trans_le (imaginary_gaussian_denominator t)
  calc
    ‖z t‖ ≤ ‖-(B : ℂ) / ((t : ℂ) + Complex.I * (h : ℂ))‖ +
      ‖Complex.I * (h : ℂ)‖ := norm_sub_le _ _
    _ = B / ‖(t : ℂ) + Complex.I * (h : ℂ)‖ + h := by
      simp [Complex.norm_real, abs_of_pos B_pos, abs_of_pos h_pos_e]
    _ ≤ B / h + h := add_le_add
      (div_le_div_of_nonneg_left B_pos.le h_pos_e (imaginary_gaussian_denominator t)) le_rfl

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
  have hb' := b_pos_e
  have hh' := h_pos_e
  have hB' := B_pos
  have hl := lambda_bound t
  have hz := z_bound t
  gcongr


lemma densityBound_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity

lemma v_bound' (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ densityBound := by
  apply (v_bound_e n j ht).trans
  unfold densityBound
  nlinarith [Real.pi_gt_three]

lemma density_bound (p : CardinalData) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖density p j t‖ ≤ densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => summand_bound_e p.x n j ht)
    exact (X_summable_pairs_e p.x).mul_left densityBound
  have hsum : ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)‖ ≤ densityBound * ‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityBound * (|p.x (n, false)| + |p.x (n, true)|) :=
        hnorm.tsum_le_tsum (fun n => summand_bound_e p.x n j ht)
          ((X_summable_pairs_e p.x).mul_left densityBound)
      _ = densityBound * ‖p.x‖ := by rw [tsum_mul_left, ← X_norm_e]
  unfold density
  calc
    _ ≤ ‖(p.c₀ : ℂ) * u 0 j t‖ + ‖(p.d₀ : ℂ) * v 0 j t‖ +
      ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| * densityBound + |p.d₀| * densityBound + densityBound * ‖p.x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exacts [u_bound_e _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring


lemma kernelEnvelope_nonneg (ell : ℕ) (s : ℝ) : 0 ≤ kernelEnvelope ell s := by
  have := b_pos_e
  have := h_pos_e
  have := B_pos
  unfold kernelEnvelope
  positivity

lemma kernelMoment_bound' (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖kernelMoment ell s t‖ ≤ kernelEnvelope ell s := by
  apply kernelMoment_bound ell hs
  rw [abs_of_nonneg ht.1]
  exact ht.2

lemma atomic_bound (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Pcoeff 0 * kernelMoment ell s 0 +
      ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ ≤
      25 * kernelEnvelope ell s := by
  have hzero : ‖Pcoeff 0 * kernelMoment ell s 0‖ ≤ 5 * kernelEnvelope ell s := by
    rw [norm_mul, Pcoeff_norm_e]
    apply mul_le_mul_of_nonneg_left (kernelMoment_bound' ell hs (by simp)) (by norm_num [coeffMass])
  have hsum : ‖∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ ≤
      20 * kernelEnvelope ell s := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 6, ‖2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 6, 2 * ‖Pcoeff j‖ * kernelEnvelope ell s := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        gcongr
        apply kernelMoment_bound' ell hs
        have hju : (j : ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
        constructor
        · positivity
        · linarith
      _ = 20 * kernelEnvelope ell s := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, positive_coeff_mass_e]
        ring
  exact (norm_add_le _ _).trans (by linarith)

lemma integral_piece_bound (p : CardinalData) (ell j : ℕ) (hj : j < 6)
    {s : ℝ} (hs : 0 ≤ s) :
    ‖∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ ≤
      densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s / 6 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => density p j t * kernelMoment ell s t)
    (a := (j : ℝ)/6) (b := ((j : ℝ)+1)/6)
    (C := densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s) ?_
  · convert hb using 1
    all_goals try with_reducible_and_instances rfl
    rw [show ((j : ℝ)+1)/6 - (j : ℝ)/6 = 1/6 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 1/6)]
    ring
  · intro t ht
    have htr := piece_interval_e hj (Set.uIoc_subset_uIcc ht)
    rw [norm_mul]
    exact mul_le_mul (density_bound p j htr) (kernelMoment_bound' ell hs htr)
      (norm_nonneg _) (by have := densityBound_nonneg; positivity)


lemma K_bound (p : CardinalData) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K p ell s| ≤
      (25 * |p.C| + densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖)) * kernelEnvelope ell s := by
  have hatom : ‖(p.C : ℂ) * (Pcoeff 0 * kernelMoment ell s 0 +
      ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ)/6))‖ ≤
      25 * |p.C| * kernelEnvelope ell s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |p.C| * (25 * kernelEnvelope ell s) := by
        gcongr; exact atomic_bound ell hs
      _ = _ := by ring
  have hsum : ‖∑ j ∈ Finset.range 6,
      ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ ≤
      densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s := by
    calc
      _ ≤ ∑ j ∈ Finset.range 6,
        ‖∫ t in (j : ℝ)/6..((j : ℝ)+1)/6, density p j t * kernelMoment ell s t‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range 6,
        (densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) * kernelEnvelope ell s / 6) := by
        exact Finset.sum_le_sum fun j hj => integral_piece_bound p ell j (Finset.mem_range.mp hj) hs
      _ = _ := by simp <;> ring
  unfold K
  exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by nlinarith))


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

lemma nodeWeight_pos (n : ℕ) : 0 < nodeWeight n := by
  unfold nodeWeight
  exact div_pos (by positivity) (Q_pos n)

lemma nodeWeight_le (n : Node) : nodeWeight n.val ≤ allNodeWeight := by
  have he : nodeWeight n.val = nodeWeight (n.val % 12) := by rw [nodeWeight, nodeWeight, Q_mod, D_mod]
  rw [he]
  exact Finset.single_le_sum (fun a _ => (nodeWeight_pos a).le) n.property.2

lemma K_positive_bound (x : X) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K (positiveData x) ell s| ≤ densityBound * ‖x‖ * kernelEnvelope ell s := by
  simpa [positiveData] using K_bound (positiveData x) ell hs

lemma Scoords_bound (x : X) (ni : Node × Bool) :
    |Scoords x ni| ≤ allNodeWeight * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
  have he0 := kernelEnvelope_nonneg 0 (ni.1.val : ℝ)
  have he1 := kernelEnvelope_nonneg 1 (ni.1.val : ℝ)
  have hd := densityBound_nonneg
  have hx := norm_nonneg x
  have hq := Q_pos ni.1.val
  have hc0 := K_positive_bound x 0 (Nat.cast_nonneg ni.1.val)
  have hc1 := K_positive_bound x 1 (Nat.cast_nonneg ni.1.val)
  have hlocal : |Scoords x ni| ≤ nodeWeight ni.1.val * densityBound * ‖x‖ *
      (kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
    unfold Scoords nodeWeight
    split
    · rw [abs_div, abs_of_pos hq]
      calc
        _ ≤ (|D ni.1.val| * |K (positiveData x) 0 ni.1.val| +
          |K (positiveData x) 1 ni.1.val|) / Q ni.1.val := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact (abs_sub _ _).trans (by rw [abs_mul])
        _ ≤ (|D ni.1.val| * (densityBound * ‖x‖ * kernelEnvelope 0 ni.1.val) +
          densityBound * ‖x‖ * kernelEnvelope 1 ni.1.val) / Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val))
            (mul_nonneg (mul_nonneg hd hx) he1), mul_nonneg (mul_nonneg hd hx) he0]
    · rw [abs_div, abs_neg, abs_of_pos hq]
      calc
        _ ≤ (densityBound * ‖x‖ * kernelEnvelope 0 ni.1.val) / Q ni.1.val := by gcongr
        _ ≤ _ := by
          apply (div_le_iff₀ hq).mpr
          field_simp
          nlinarith [mul_nonneg (abs_nonneg (D ni.1.val))
            (mul_nonneg (mul_nonneg hd hx) (add_nonneg he0 he1)),
            mul_nonneg (mul_nonneg hd hx) he1]
  exact hlocal.trans (by gcongr; exact nodeWeight_le ni.1)


lemma exp_nat_summable : Summable (fun n : ℕ => Real.exp (-kappa * n)) := by
  have he : Real.exp (-kappa) < 1 := by rw [Real.exp_lt_one_iff]; linarith [kappa_pos]
  have hh := summable_geometric_of_lt_one (Real.exp_pos (-kappa)).le he
  simpa only [← Real.exp_nat_mul, mul_comm] using hh

lemma kernelEnvelope_summable (ell : ℕ) : Summable (fun n : Node => kernelEnvelope ell n.val) := by
  have hh := exp_nat_summable.comp_injective (i := fun n : Node => n.val) Subtype.val_injective
  exact hh.mul_left ((1/(b*h)) * (Real.pi*(B/h+h))^ell)

lemma pairEnvelope_summable : Summable (fun ni : Node × Bool =>
    kernelEnvelope 0 ni.1.val + kernelEnvelope 1 ni.1.val) := by
  apply (summable_prod_of_nonneg (fun ni =>
    add_nonneg (kernelEnvelope_nonneg _ _) (kernelEnvelope_nonneg _ _))).mpr
  constructor
  · intro n; exact Summable.of_finite
  · simpa only [tsum_bool] using
      ((kernelEnvelope_summable 0).add (kernelEnvelope_summable 1)).add
        ((kernelEnvelope_summable 0).add (kernelEnvelope_summable 1))

lemma Scoords_summable (x : X) : Summable (fun ni : Node × Bool => |Scoords x ni|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun ni => Scoords_bound x ni)
  exact pairEnvelope_summable.mul_left (allNodeWeight * densityBound * ‖x‖)

lemma Scoords_mem_e_oai (x : X) : Memℓp (Scoords x) 1 := by
  apply memℓp_gen
  simpa using Scoords_summable x

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Scoords_mem_e_oai := @OAI.SharpPlanar.Scoords_mem_e_oai
