-- Prove2me | solution 1 for MasulloRepair.EulerScale.finite_prime_blaschke_product_delay_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T23:42:21.058916+00:00
-- url     : https://prove2.me/submissions/d69e90e6-f8f8-4867-b8f0-8cdf0c44d4fe

import Mathlib

/-!+# Quantitative delay limit for the finite rational Euler Blaschke product

This file proves a finite comparison for the literal factors
`(exp (-L*z) - r)/(1-r*exp (-L*z))`, with real `0 ≤ r < 1`.
It does not identify the finite-band geometric projections in Masullo's manuscript.
-/

open scoped BigOperators
open Complex Set

namespace MasulloRepair.EulerScale

noncomputable def diskFactor (r : ℝ) (a : ℂ) : ℂ :=
  (a - (r : ℂ)) / (1 - (r : ℂ) * a)

lemma denominator_lower {r : ℝ} {a : ℂ} (hr : 0 ≤ r) (ha : ‖a‖ ≤ 1) :
    1 - r ≤ ‖1 - (r : ℂ) * a‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * a)
  simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr] at h
  have hmul := mul_le_mul_of_nonneg_left ha hr
  linarith

lemma denominator_ne_zero {r : ℝ} {a : ℂ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ha : ‖a‖ ≤ 1) :
    1 - (r : ℂ) * a ≠ 0 := by
  have h := denominator_lower hr ha
  intro hz
  rw [hz, norm_zero] at h
  linarith

lemma diskFactor_norm_le_one {r : ℝ} {a : ℂ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ha : ‖a‖ ≤ 1) :
    ‖diskFactor r a‖ ≤ 1 := by
  have hn : 0 < ‖1 - (r : ℂ) * a‖ := norm_pos_iff.mpr (denominator_ne_zero hr hr1 ha)
  have hid : Complex.normSq (1 - (r : ℂ) * a) - Complex.normSq (a - (r : ℂ)) =
      (1 - r ^ 2) * (1 - Complex.normSq a) := by
    simp [Complex.normSq_apply]
    ring
  have har : Complex.normSq a ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hrr : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hdiff := mul_nonneg hrr (sub_nonneg.mpr har)
  rw [← hid, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hdiff
  have hle : ‖a - (r : ℂ)‖ ≤ ‖1 - (r : ℂ) * a‖ := by
    nlinarith [norm_nonneg (a - (r : ℂ))]
  rw [diskFactor, norm_div]
  exact (div_le_one hn).mpr hle

lemma diskFactor_sub_self_bound {r R : ℝ} {a : ℂ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) (ha : ‖a‖ ≤ 1) :
    ‖diskFactor r a - a‖ ≤ (2 * r / (1 - R)) * ‖a - 1‖ := by
  have hden := denominator_ne_zero hr (lt_of_le_of_lt hrR hR) ha
  have hid : diskFactor r a - a =
      (r : ℂ) * (a - 1) * (a + 1) / (1 - (r : ℂ) * a) := by
    apply (eq_div_iff hden).mpr
    unfold diskFactor
    rw [sub_mul, div_mul_cancel₀ _ hden]
    ring
  have hlow : 1 - R ≤ ‖1 - (r : ℂ) * a‖ := by
    have := denominator_lower hr ha
    linarith
  have ha1 : ‖a + 1‖ ≤ 2 := by
    calc
      ‖a + 1‖ ≤ ‖a‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by simpa only [norm_one] using (show ‖a‖ + 1 ≤ 2 by linarith)
  rw [hid, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]
  calc
    r * ‖a - 1‖ * ‖a + 1‖ / ‖1 - (r : ℂ) * a‖
        ≤ r * ‖a - 1‖ * 2 / ‖1 - (r : ℂ) * a‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha1 (by positivity))
        (norm_nonneg _)
    _ ≤ r * ‖a - 1‖ * 2 / (1 - R) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hlow
    _ = (2 * r / (1 - R)) * ‖a - 1‖ := by ring

lemma norm_exp_neg_sub_one_le {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.exp (-z) - 1‖ ≤ ‖z‖ := by
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) * z))
      (Complex.exp (-(t : ℂ) * z) * (-z)) t := by
    convert ((Complex.ofRealCLM.hasDerivAt).neg.mul_const z).cexp using 1 <;> simp
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖Complex.exp (-(t : ℂ) * z) * (-z)‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_neg, Complex.norm_exp]
    have hexp : Real.exp (-(t : ℂ) * z).re ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, zero_mul, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) hz
    exact mul_le_of_le_one_left (norm_nonneg _) hexp
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) hb
  simpa using h

lemma norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hpg : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      calc
        ‖∏ i ∈ s, g i‖ ≤ ∏ i ∈ s, ‖g i‖ := Finset.norm_prod_le _ _
        _ ≤ 1 := Finset.prod_le_one (fun i _ => norm_nonneg _) hgs
    calc
      ‖f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i)‖ =
          ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
            (f a - g a) * ∏ i ∈ s, g i‖ := by congr 1; ring
      _ ≤ ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ +
          ‖(f a - g a) * ∏ i ∈ s, g i‖ := norm_add_le _ _
      _ ≤ ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ + ‖f a - g a‖ := by
        simp only [norm_mul]
        exact add_le_add
          (mul_le_of_le_one_left (norm_nonneg _) (hf a (Finset.mem_insert_self _ _)))
          (mul_le_of_le_one_right (norm_nonneg _) hpg)
      _ ≤ ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by linarith [ih hfs hgs]

/-- The quantitative finite comparison, including the boundary of the right half-plane. -/
theorem finite_euler_product_delay_bound {ι : Type*} (s : Finset ι)
    (L r : ι → ℝ) (η R : ℝ) (z : ℂ)
    (hL : ∀ i ∈ s, 0 ≤ L i) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hrR : ∀ i ∈ s, r i ≤ R) (hR : R < 1) (hη : 0 ≤ η) (hz : 0 ≤ z.re) :
    ‖(∏ i ∈ s, diskFactor (r i) (Complex.exp (-((η * L i : ℝ) : ℂ) * z))) -
        Complex.exp (-((η * ∑ i ∈ s, L i : ℝ) : ℂ) * z)‖ ≤
      (2 * η * ‖z‖ / (1 - R)) * ∑ i ∈ s, r i * L i := by
  classical
  let a : ι → ℂ := fun i => Complex.exp (-((η * L i : ℝ) : ℂ) * z)
  have ha (i : ι) (hi : i ∈ s) : ‖a i‖ ≤ 1 := by
    change ‖Complex.exp (-((η * L i : ℝ) : ℂ) * z)‖ ≤ 1
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hη (hL i hi)) hz)
  have herror (i : ι) (hi : i ∈ s) :
      ‖diskFactor (r i) (a i) - a i‖ ≤
        (2 * η * ‖z‖ / (1 - R)) * (r i * L i) := by
    have hz' : 0 ≤ (((η * L i : ℝ) : ℂ) * z).re := by
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (mul_nonneg hη (hL i hi)) hz
    have he := norm_exp_neg_sub_one_le hz'
    have he' : ‖a i - 1‖ ≤ η * L i * ‖z‖ := by
      simpa only [a, neg_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hη, abs_of_nonneg (hL i hi)] using he
    calc
      ‖diskFactor (r i) (a i) - a i‖ ≤ (2 * r i / (1 - R)) * ‖a i - 1‖ :=
        diskFactor_sub_self_bound (hr i hi) (hrR i hi) hR (ha i hi)
      _ ≤ (2 * r i / (1 - R)) * (η * L i * ‖z‖) :=
        mul_le_mul_of_nonneg_left he' (div_nonneg (mul_nonneg (by norm_num) (hr i hi)) (by linarith))
      _ = (2 * η * ‖z‖ / (1 - R)) * (r i * L i) := by ring
  have hprod : (∏ i ∈ s, a i) =
      Complex.exp (-((η * ∑ i ∈ s, L i : ℝ) : ℂ) * z) := by
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← Complex.ofReal_sum, ← Finset.mul_sum]
  calc
    _ = ‖(∏ i ∈ s, diskFactor (r i) (a i)) - ∏ i ∈ s, a i‖ := by rw [hprod]
    _ ≤ ∑ i ∈ s, ‖diskFactor (r i) (a i) - a i‖ :=
      norm_prod_sub_prod_le_sum s _ _
        (fun i hi => diskFactor_norm_le_one (hr i hi) (lt_of_le_of_lt (hrR i hi) hR) (ha i hi)) ha
    _ ≤ ∑ i ∈ s, (2 * η * ‖z‖ / (1 - R)) * (r i * L i) := Finset.sum_le_sum herror
    _ = _ := (Finset.mul_sum _ _ _).symm

#print axioms finite_euler_product_delay_bound

end MasulloRepair.EulerScale

open MasulloRepair.EulerScale

/-- The literal finite rational-prime product, at the reciprocal log-primorial scale.
The attenuation parameter `κ` is fixed and strictly positive. -/
theorem solution (s : Finset ℕ)
    (hs : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (κ : ℝ) (hκ : 0 < κ)
    (z : ℂ) (hz : 0 ≤ z.re) :
    let θ : ℝ := ∑ p ∈ s, Real.log p
    ‖(∏ p ∈ s,
        (Complex.exp (-((Real.log p / θ : ℝ) : ℂ) * z) -
          (Real.exp (-κ * Real.log p) : ℂ)) /
        (1 - (Real.exp (-κ * Real.log p) : ℂ) *
          Complex.exp (-((Real.log p / θ : ℝ) : ℂ) * z))) - Complex.exp (-z)‖ ≤
      (2 * ‖z‖ / (1 - Real.exp (-κ * Real.log 2))) *
        ((∑ p ∈ s, Real.exp (-κ * Real.log p) * Real.log p) / θ) := by
  classical
  dsimp only
  let θ : ℝ := ∑ p ∈ s, Real.log p
  have hlog (p : ℕ) (hps : p ∈ s) : 0 < Real.log p := by
    apply Real.log_pos
    exact_mod_cast (hp p hps).one_lt
  have hθ : 0 < θ := by
    exact Finset.sum_pos hlog hs
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR : Real.exp (-κ * Real.log 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hκ) h2
  have hrR (p : ℕ) (hps : p ∈ s) :
      Real.exp (-κ * Real.log p) ≤ Real.exp (-κ * Real.log 2) := by
    rw [Real.exp_le_exp]
    have hge : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hps).two_le
    have hlogs := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hge
    exact mul_le_mul_of_nonpos_left hlogs (by linarith)
  have h := finite_euler_product_delay_bound s (fun p => Real.log p)
    (fun p => Real.exp (-κ * Real.log p)) θ⁻¹ (Real.exp (-κ * Real.log 2)) z
    (fun p hps => (hlog p hps).le) (fun _ _ => (Real.exp_pos _).le) hrR hR
    (inv_nonneg.mpr hθ.le) hz
  have hη : θ⁻¹ * ∑ p ∈ s, Real.log p = 1 := inv_mul_cancel₀ (ne_of_gt hθ)
  rw [hη] at h
  simp only [Complex.ofReal_one, neg_one_mul] at h
  convert h using 1
  · apply congrArg (fun w : ℂ => ‖w - Complex.exp (-z)‖)
    apply Finset.prod_congr rfl
    intro p hps
    dsimp only [diskFactor]
    have hratio : Real.log p / (∑ q ∈ s, Real.log q) = θ⁻¹ * Real.log p := by
      dsimp only [θ]
      ring
    rw [hratio]
  · dsimp only [θ]
    ring


#print axioms solution
