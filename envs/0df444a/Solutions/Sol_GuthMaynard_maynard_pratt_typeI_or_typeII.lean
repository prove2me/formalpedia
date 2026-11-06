-- Prove2me | solution 1 for GuthMaynard.maynard_pratt_typeI_or_typeII
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:34:56.33003+00:00
-- url     : https://prove2.me/submissions/d20300c5-a0ee-43ce-ab76-11ca62f42956

import Mathlib

/-!
# Maynard–Pratt Lemma 23 (arXiv:2206.11729v2, Appendix C)

Assembled from MP23PartA/Z/B/C/D and the blueprint assembly.
-/

-- ===== Part A =====

/-! Part A: analytic generalities (zeros in the strip, Γ decay, contour shift across a pole). -/

open Complex MeasureTheory Filter Topology Set

namespace GuthMaynard.CitedZeros.MP23

/-- Nontrivial zeros lie in the open critical strip. -/
lemma zero_re_pos_lt_one {ρ : ℂ} (h : riemannZeta ρ = 0) (hi : ρ.im ≠ 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra hre
    push Not at hre
    set s : ℂ := 1 - ρ with hs
    have hsre : 1 ≤ s.re := by simp [hs]; linarith
    have hsim : s.im ≠ 0 := by simp [hs]; exact hi
    have hn : ∀ n : ℕ, s ≠ -n := by
      intro n hn; apply hsim; rw [hn]; simp
    have h1 : s ≠ 1 := by intro h1; apply hsim; rw [h1]; simp
    have hfe := riemannZeta_one_sub hn h1
    rw [hs, sub_sub_cancel, ← hs] at hfe
    rw [h] at hfe
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hsre
    have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hn
    have hc : Complex.cos (↑Real.pi * s / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      apply hsim
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hs' : s = 2 * (k : ℂ) + 1 := by
        apply mul_left_cancel₀ hpi
        linear_combination 2 * hk
      rw [hs']; simp
    have hp : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      push Not
      intro h0
      exfalso
      have : (2 * (Real.pi : ℂ)) ≠ 0 := by
        exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact this h0
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hp) hG) hc) hz) hfe.symm
  · by_contra hre
    push Not at hre
    exact riemannZeta_ne_zero_of_one_le_re hre h

lemma norm_Gamma_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc a b, Real.Gamma x ≤ C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx => ha.trans_le hx.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

theorem gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Complex.Gamma (z + n) = Complex.Gamma z * ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, natCast_im, add_zero, zero_im] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hn, ih, Finset.prod_range_succ]
    ring

theorem gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := real_Gamma_compact_bound (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by
    simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Complex.Gamma z‖ :=
      mul_le_mul_of_nonneg_right (gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Complex.Gamma (z + n)‖ := by rw [gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

/-- Polynomial decay of `Γ` in vertical strips. -/
lemma gamma_decay (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → (1 + |z.im|) ^ n * ‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := real_Gamma_compact_bound a b ha
  refine ⟨2 ^ n * (C₀ + C₁), by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · have hp : (1 + |z.im|) ^ n ≤ 2 ^ n * |z.im| ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ n * |z.im| ^ n) * ‖Complex.Gamma z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ n * C₁ := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlarge z hza hzb ht) (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have hg : ‖Complex.Gamma z‖ ≤ C₀ :=
      (norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza, hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

lemma one_add_sq_le (u : ℝ) : 1 + u ^ 2 ≤ (1 + |u|) ^ 2 := by
  nlinarith [sq_abs u, abs_nonneg u]

/-- `|Γ(z)| ≤ C / (1 + (Im z)^2)` in the strip `a ≤ Re z ≤ b`, `a > 0`. -/
lemma gamma_sq_decay (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C, hC, h⟩ := gamma_decay a b ha 2
  refine ⟨C, hC, fun z hza hzb => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  have := h z hza hzb
  have h2 := one_add_sq_le z.im
  nlinarith [norm_nonneg (Complex.Gamma z)]

/-- Uniform bound for `∫ |Γ|` on the vertical lines we need. -/
lemma gamma_line_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, (σ = -1 / 2 ∨ σ ∈ Icc (1 / 2 : ℝ) 3) →
    ‖∫ u : ℝ, Complex.Gamma ((σ : ℂ) + (u : ℂ) * I)‖ ≤ K := by
  obtain ⟨C, hC, h⟩ := gamma_sq_decay (1 / 2) 3 (by norm_num)
  refine ⟨2 * C * Real.pi, by positivity, ?_⟩
  intro σ hσ
  have hb : ∀ u : ℝ, ‖Complex.Gamma ((σ : ℂ) + (u : ℂ) * I)‖ ≤ (2 * C) * (1 + u ^ 2)⁻¹ := by
    intro u
    rcases hσ with hσ | hσ
    · subst hσ
      set z : ℂ := (((-1 / 2 : ℝ)) : ℂ) + (u : ℂ) * I with hz
      have hzre : z.re = -1 / 2 := by simp [hz]
      have hz0 : z ≠ 0 := by intro h0; rw [h0] at hzre; norm_num at hzre
      have hn : (1 / 2 : ℝ) ≤ ‖z‖ := by
        have := Complex.abs_re_le_norm z
        rw [hzre] at this; norm_num at this; linarith
      have hΓ : ‖Complex.Gamma z‖ ≤ 2 * ‖Complex.Gamma (z + 1)‖ := by
        rw [Complex.Gamma_add_one z hz0, norm_mul]
        nlinarith [norm_nonneg (Complex.Gamma z)]
      have h1 := h (z + 1) (by simp [hzre]; norm_num) (by simp [hzre]; norm_num)
      have him : (z + 1).im = u := by simp [hz]
      rw [him] at h1
      calc ‖Complex.Gamma z‖ ≤ 2 * ‖Complex.Gamma (z + 1)‖ := hΓ
        _ ≤ 2 * (C / (1 + u ^ 2)) := by gcongr
        _ = _ := by ring
    · have h1 := h ((σ : ℂ) + (u : ℂ) * I) (by simp; linarith [hσ.1]) (by simp; linarith [hσ.2])
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at h1
      calc _ ≤ C / (1 + u ^ 2) := h1
        _ ≤ 2 * C / (1 + u ^ 2) := by gcongr; linarith
        _ = _ := by ring
  have hint := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul (2 * C))
    (ae_of_all _ hb)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hint
  exact hint

/-! ### Contour shift -/

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert horizontal_integral_tendsto_zero g a b C hab hg using 1
    funext t
    simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      have hz' : z.re ∈ Icc a b := by
        simpa [uIcc_of_le hab] using hz.1
      exact (hdiff z hz'.1 hz'.2).differentiableWithinAt
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

/-- A bound valid for large heights extends to the whole closed strip by compactness. -/
lemma strip_bound (φ : ℂ → ℂ) (a b C H : ℝ)
    (hc : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ContinuousAt φ z)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) :
    ∃ C' : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖φ z‖ ≤ C' / (1 + z.im ^ 2) := by
  let K : Set ℂ := Icc a b ×ℂ Icc (-H) H
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hw : ContinuousOn (fun z : ℂ => (1 + z.im ^ 2) * ‖φ z‖) K := by
    intro z hz
    exact ((continuous_const.add (continuous_im.pow 2)).continuousAt.mul
      (hc z hz.1.1 hz.1.2).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hw
  refine ⟨max B C, fun z hza hzb => ?_⟩
  by_cases ht : H ≤ |z.im|
  · exact (hd z hza hzb ht).trans (by gcongr; exact le_max_right _ _)
  · have hzK : z ∈ K := ⟨⟨hza, hzb⟩, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    have := hB (Set.mem_image_of_mem _ hzK)
    rw [le_div_iff₀ (by positivity)]
    have h2 : (1 + z.im ^ 2) * ‖φ z‖ ≤ max B C := this.trans (le_max_left _ _)
    linarith

lemma line_integrable (φ : ℂ → ℂ) (x C : ℝ)
    (hc : ∀ u : ℝ, ContinuousAt φ ((x : ℂ) + (u : ℂ) * I))
    (hb : ∀ u : ℝ, ‖φ ((x : ℂ) + (u : ℂ) * I)‖ ≤ C / (1 + u ^ 2)) :
    Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
  have hcont : Continuous (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact ContinuousAt.comp (g := φ) (hc u)
      (by fun_prop : ContinuousAt (fun u : ℝ => (x : ℂ) + (u : ℂ) * I) u)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  apply ae_of_all
  intro u
  simpa [div_eq_mul_inv] using hb u

/-- Integrability on a vertical line from continuity and a large-height bound. -/
lemma line_integrable' (φ : ℂ → ℂ) (x C H : ℝ)
    (hc : ∀ u : ℝ, ContinuousAt φ ((x : ℂ) + (u : ℂ) * I))
    (hd : ∀ z : ℂ, x ≤ z.re → z.re ≤ x → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) :
    Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
  have hc' : ∀ z : ℂ, x ≤ z.re → z.re ≤ x → ContinuousAt φ z := by
    intro z h1 h2
    have hz : z = (x : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp <;> linarith
    rw [hz]; exact hc _
  obtain ⟨C', hC'⟩ := strip_bound φ x x C H hc' hd
  refine line_integrable φ x C' hc (fun u => ?_)
  have := hC' ((x : ℂ) + (u : ℂ) * I) (by simp) (by simp)
  simpa using this

/-- Contour shift across one simple pole, comparing with a reference function `g` of residue 1. -/
lemma shift_pole (f g : ℂ → ℂ) (a b : ℝ) (s₀ R : ℂ) (ha : a < s₀.re) (hb : s₀.re < b)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ f z)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ g z)
    (hfl : Tendsto (fun z => (z - s₀) * f z) (𝓝[≠] s₀) (𝓝 R))
    (hgl : Tendsto (fun z => (z - s₀) * g z) (𝓝[≠] s₀) (𝓝 1))
    (hfd : ∃ C H : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖f z‖ ≤ C / (1 + z.im ^ 2))
    (hgd : ∃ C H : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖g z‖ ≤ C / (1 + z.im ^ 2)) :
    (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * I)) - ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * I) =
      R * ((∫ u : ℝ, g ((a : ℂ) + (u : ℂ) * I)) - ∫ u : ℝ, g ((b : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨Cf, Hf, hfd⟩ := hfd
  obtain ⟨Cg, Hg, hgd⟩ := hgd
  have hab : a ≤ b := by linarith
  set h : ℂ → ℂ := fun z => f z - R * g z with hh
  set h' : ℂ → ℂ := Function.update h s₀ ((𝓝[≠] s₀).limUnder h) with hh'
  -- the open strip around `s₀`
  set U : Set ℂ := {z : ℂ | a < z.re ∧ z.re < b} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  have hUs : U ∈ 𝓝 s₀ := hUo.mem_nhds ⟨ha, hb⟩
  have hhd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ h z :=
    fun z h1 h2 h3 => (hf z h1 h2 h3).sub ((hg z h1 h2 h3).const_mul R)
  have hlim : Tendsto (fun z => (z - s₀) * h z) (𝓝[≠] s₀) (𝓝 0) := by
    have := hfl.sub (hgl.const_mul R)
    simp only [mul_one, sub_self] at this
    refine this.congr (fun z => ?_)
    simp only [hh]; ring
  have hlo : (fun z => h z - h s₀) =o[𝓝[≠] s₀] fun z => (z - s₀)⁻¹ := by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have h2 : Tendsto (fun z => (z - s₀) * h s₀) (𝓝[≠] s₀) (𝓝 0) := by
        have : Tendsto (fun z : ℂ => z - s₀) (𝓝[≠] s₀) (𝓝 0) := by
          have h0 : Tendsto (fun z : ℂ => z - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
            tendsto_id.sub_const s₀
          rw [sub_self] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        simpa using this.mul_const (h s₀)
      have := hlim.sub h2
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - s₀ ≠ 0 := sub_ne_zero.mpr hz
      field_simp
    · filter_upwards [self_mem_nhdsWithin] with z hz h0
      exact absurd h0 (inv_ne_zero (sub_ne_zero.mpr hz))
  have hdon : DifferentiableOn ℂ h (U \ {s₀}) := by
    intro z hz
    exact (hhd z hz.1.1.le hz.1.2.le hz.2).differentiableWithinAt
  have hD := Complex.differentiableOn_update_limUnder_of_isLittleO hUs hdon hlo
  have hh'd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ h' z := by
    intro z h1 h2
    by_cases hz : z = s₀
    · subst hz
      exact hD.differentiableAt hUs
    · have heq : h' =ᶠ[𝓝 z] h := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
        simp only [hh']
        exact Function.update_of_ne hw _ _
      exact (hhd z h1 h2 hz).congr_of_eventuallyEq heq
  -- large-height bound for `h'`
  set H := max (max Hf Hg) (|s₀.im| + 1) with hH
  have hh'b : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| →
      ‖h' z‖ ≤ (Cf + ‖R‖ * Cg) / (1 + z.im ^ 2) := by
    intro z h1 h2 h3
    have hz : z ≠ s₀ := by
      intro hz; rw [hz] at h3
      have : |s₀.im| + 1 ≤ H := le_max_right _ _
      linarith
    have : h' z = h z := by simp only [hh']; exact Function.update_of_ne hz _ _
    rw [this]
    have e1 := hfd z h1 h2 (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h3)
    have e2 := hgd z h1 h2 (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h3)
    calc ‖h z‖ ≤ ‖f z‖ + ‖R‖ * ‖g z‖ := by
          simp only [hh]; exact (norm_sub_le _ _).trans (by rw [norm_mul])
      _ ≤ Cf / (1 + z.im ^ 2) + ‖R‖ * (Cg / (1 + z.im ^ 2)) := by gcongr
      _ = _ := by ring
  obtain ⟨C', hC'⟩ := strip_bound h' a b _ H (fun z h1 h2 => (hh'd z h1 h2).continuousAt) hh'b
  -- integrability of `f`, `g` on the two lines
  have hne : ∀ x : ℝ, x ≠ s₀.re → ∀ u : ℝ, (x : ℂ) + (u : ℂ) * I ≠ s₀ := by
    intro x hx u he; apply hx; rw [← he]; simp
  have hint : ∀ φ : ℂ → ℂ, (∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ s₀ → DifferentiableAt ℂ φ z) →
      ∀ C H : ℝ, (∀ z : ℂ, a ≤ z.re → z.re ≤ b → H ≤ |z.im| → ‖φ z‖ ≤ C / (1 + z.im ^ 2)) →
      ∀ x : ℝ, a ≤ x → x ≤ b → x ≠ s₀.re → Integrable (fun u : ℝ => φ ((x : ℂ) + (u : ℂ) * I)) := by
    intro φ hφ C H hφb x hx1 hx2 hx3
    refine line_integrable' φ x C H (fun u => (hφ _ (by simpa using hx1) (by simpa using hx2)
      (hne x hx3 u)).continuousAt) (fun z h1 h2 h3 => hφb z (by linarith) (by linarith) h3)
  have hfa := hint f hf Cf Hf hfd a le_rfl hab (by linarith)
  have hfb := hint f hf Cf Hf hfd b hab le_rfl (by linarith)
  have hga := hint g hg Cg Hg hgd a le_rfl hab (by linarith)
  have hgb := hint g hg Cg Hg hgd b hab le_rfl (by linarith)
  have hline : ∀ x : ℝ, x ≠ s₀.re → (fun u : ℝ => h' ((x : ℂ) + (u : ℂ) * I)) =
      fun u : ℝ => f ((x : ℂ) + (u : ℂ) * I) - R * g ((x : ℂ) + (u : ℂ) * I) := by
    intro x hx; funext u
    simp only [hh']
    rw [Function.update_of_ne (hne x hx u)]
  have hh'a : Integrable (fun u : ℝ => h' ((a : ℂ) + (u : ℂ) * I)) := by
    rw [hline a (by linarith)]; exact hfa.sub (hga.const_mul R)
  have hh'bb : Integrable (fun u : ℝ => h' ((b : ℂ) + (u : ℂ) * I)) := by
    rw [hline b (by linarith)]; exact hfb.sub (hgb.const_mul R)
  have hmain := integral_eq_of_strip_decay h' a b C' hab hh'd hh'a hh'bb
    (fun σ (hσ : σ ∈ Icc a b) t => by
      simpa using hC' ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ.1) (by simpa using hσ.2))
  rw [hline a (by linarith), hline b (by linarith), integral_sub hfa (hga.const_mul R),
    integral_sub hfb (hgb.const_mul R), integral_const_mul, integral_const_mul] at hmain
  linear_combination hmain

end GuthMaynard.CitedZeros.MP23

-- ===== Part Z =====

/-! Part Z: polynomial growth of `ζ` for `Re w ≥ 1/2`. -/

open Complex MeasureTheory Filter Topology Set

namespace GuthMaynard.CitedZeros.MP23

/-- Terms of the continuation `(w-1) ζ(w) = -1 + ∑ eT w n`. -/
noncomputable def eT (w : ℂ) (n : ℕ) : ℂ :=
  (w - 1) * ((n : ℂ) + 1) ^ (-w) - ((n : ℂ) + 1) ^ (1 - w) + ((n : ℂ) + 2) ^ (1 - w)

lemma cpow_diff_bound (w : ℂ) (hw : 0 < w.re) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : y ∈ Icc x (x + 1)) :
    ‖(y : ℂ) ^ (-w) - (x : ℂ) ^ (-w)‖ ≤ ‖w‖ * x ^ (-w.re - 1) * (y - x) := by
  have hderiv : ∀ t ∈ Icc x (x + 1), HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ (-w))
      ((-w) * (t : ℂ) ^ (-w - 1)) (Icc x (x + 1)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (hasDerivAt_ofReal_cpow_const ht0 (by
      intro h; apply (ne_of_gt hw); have := congrArg Complex.re h; simpa using this)).hasDerivWithinAt
  have hb : ∀ t ∈ Ico x (x + 1), ‖(-w) * (t : ℂ) ^ (-w - 1)‖ ≤ ‖w‖ * x ^ (-w.re - 1) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)) (norm_nonneg _)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb y hy

lemma eT_bound (w : ℂ) (hw : 0 < w.re) (n : ℕ) :
    ‖eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-w.re - 1) := by
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx : 0 < x := by positivity
  rcases eq_or_ne w 1 with rfl | hw1
  · simp [eT]
  have hw1' : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  set φ : ℝ → ℂ := fun y => (w - 1) * (y : ℂ) * (x : ℂ) ^ (-w) + (y : ℂ) ^ (1 - w) with hφ
  have hderiv : ∀ t ∈ Icc x (x + 1), HasDerivWithinAt φ
      ((w - 1) * (x : ℂ) ^ (-w) + (1 - w) * (t : ℂ) ^ (-w)) (Icc x (x + 1)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 := hasDerivAt_ofReal_cpow_const ht0 hw1'
    rw [show 1 - w - 1 = -w by ring] at h1
    have h2 : HasDerivAt (fun y : ℝ => (w - 1) * (y : ℂ) * (x : ℂ) ^ (-w)) ((w - 1) * (x : ℂ) ^ (-w)) t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (w - 1)).mul_const ((x : ℂ) ^ (-w))
      simpa using this
    exact (h2.add h1).hasDerivWithinAt
  have hb : ∀ t ∈ Ico x (x + 1),
      ‖(w - 1) * (x : ℂ) ^ (-w) + (1 - w) * (t : ℂ) ^ (-w)‖ ≤ ‖w - 1‖ * (‖w‖ * x ^ (-w.re - 1)) := by
    intro t ht
    have e : (w - 1) * (x : ℂ) ^ (-w) + (1 - w) * (t : ℂ) ^ (-w) =
        -((w - 1) * ((t : ℂ) ^ (-w) - (x : ℂ) ^ (-w))) := by ring
    rw [e, norm_neg, norm_mul]
    gcongr
    calc ‖(t : ℂ) ^ (-w) - (x : ℂ) ^ (-w)‖ ≤ ‖w‖ * x ^ (-w.re - 1) * (t - x) :=
          cpow_diff_bound w hw x hx t (Ico_subset_Icc_self ht)
      _ ≤ ‖w‖ * x ^ (-w.re - 1) * 1 := by
          gcongr
          linarith [ht.2]
      _ = _ := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb (x + 1) ⟨by linarith, le_rfl⟩
  have he : φ (x + 1) - φ x = eT w n := by
    simp only [hφ, eT, hxdef]
    push_cast
    rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring]
    have hx0 : ((n : ℂ) + 1) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    have : ((n : ℂ) + 1) ^ (1 - w) = ((n : ℂ) + 1) * ((n : ℂ) + 1) ^ (-w) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hx0, Complex.cpow_one]
    rw [this]
    ring
  rw [he] at hmvt
  calc ‖eT w n‖ ≤ ‖w - 1‖ * (‖w‖ * x ^ (-w.re - 1)) * (x + 1 - x) := hmvt
    _ = _ := by ring

lemma summable_rpow_shift {p : ℝ} (hp : 1 < p) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) := by
  have := (Real.summable_one_div_nat_add_rpow 1 p).mpr hp
  refine this.congr (fun n => ?_)
  have h0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_of_pos h0, Real.rpow_neg h0.le, one_div]

lemma eT_bound' (w : ℂ) (hw : 1 / 4 < w.re) (n : ℕ) :
    ‖eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)) := by
  refine (eT_bound w (by linarith) n).trans ?_
  gcongr
  · have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact this
  · linarith

lemma eT_differentiable (n : ℕ) : Differentiable ℂ (fun w => eT w n) := by
  intro w
  have h1 : ((n : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  have h2 : ((n : ℂ) + 2) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact_mod_cast this.ne'
  unfold eT
  have d1 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (-w)) w :=
    differentiableAt_id.neg.const_cpow (Or.inl h1)
  have d2 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (1 - w)) w :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl h1)
  have d3 : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 2) ^ (1 - w)) w :=
    (differentiableAt_const _ |>.sub differentiableAt_id).const_cpow (Or.inl h2)
  exact (((differentiableAt_id.sub_const 1).mul d1).sub d2).add d3

/-- The continuation sum. -/
noncomputable def Gz (w : ℂ) : ℂ := ∑' n : ℕ, eT w n

/-- The domain `1/4 < Re w`, `|w| < R`. -/
def UR (R : ℝ) : Set ℂ := {w : ℂ | 1 / 4 < w.re} ∩ Metric.ball 0 R

lemma UR_open (R : ℝ) : IsOpen (UR R) :=
  (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball

lemma Gz_diff (R : ℝ) : DifferentiableOn ℂ Gz (UR R) := by
  have hs := (summable_rpow_shift (p := 5 / 4) (by norm_num)).mul_left ((R + 1) * R)
  refine differentiableOn_tsum_of_summable_norm hs (fun n => (eT_differentiable n).differentiableOn)
    (UR_open R) (fun n w hw => ?_)
  have hwR : ‖w‖ < R := by simpa using hw.2
  refine (eT_bound' w hw.1 n).trans ?_
  have h1 : ‖w - 1‖ ≤ R + 1 := (norm_sub_le _ _).trans (by simp; linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 hwR.le (norm_nonneg _) (by linarith [norm_nonneg w]))
    (by positivity)

lemma Gz_eq (w : ℂ) (hw : 1 < w.re) : Gz w = (w - 1) * riemannZeta w - 1 := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcast : ∀ n : ℕ, ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := fun n => by push_cast; ring
  -- summability of `(n+1)^{-w}`
  have hs1 : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (-w)) := by
    apply Summable.of_norm
    refine (summable_rpow_shift (p := w.re) hw).congr (fun n => ?_)
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (hpos n)]
    simp
  have hsG : Summable (fun n : ℕ => eT w n) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)))
    · exact (summable_rpow_shift (p := 5 / 4) (by norm_num)).mul_left _
    · intro n; exact eT_bound' w (by linarith) n
  set f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (1 - w) with hf
  have hs2 : Summable (fun n : ℕ => f (n + 1) - f n) := by
    have := hsG.sub (hs1.mul_left (w - 1))
    refine this.congr (fun n => ?_)
    simp only [eT, hf]; push_cast; ring_nf
  have hlim : Tendsto f atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : (fun n : ℕ => ‖f n‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (1 - w.re) := by
      funext n
      simp only [hf]
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (hpos n)]
      simp
    rw [e]
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := (tendsto_rpow_neg_atTop (y := w.re - 1) (by linarith)).comp h1
    refine h2.congr (fun n => ?_)
    simp only [Function.comp, neg_sub]
  have htel : ∑' n : ℕ, (f (n + 1) - f n) = -1 := by
    have hp := hs2.hasSum.tendsto_sum_nat
    have hq : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, (f (i + 1) - f i)) atTop (𝓝 (0 - f 0)) := by
      have : (fun N : ℕ => ∑ i ∈ Finset.range N, (f (i + 1) - f i)) = fun N => f N - f 0 := by
        funext N; exact Finset.sum_range_sub f N
      rw [this]; exact hlim.sub_const _
    have := tendsto_nhds_unique hp hq
    rw [this]; simp [hf]
  have hz : riemannZeta w = ∑' n : ℕ, ((n : ℂ) + 1) ^ (-w) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
    congr 1; funext n; rw [Complex.cpow_neg, one_div]
  have hsplit : (fun n : ℕ => eT w n) = fun n : ℕ => (w - 1) * ((n : ℂ) + 1) ^ (-w) + (f (n + 1) - f n) := by
    funext n; simp only [eT, hf]; push_cast; ring_nf
  unfold Gz
  rw [hsplit, (hs1.mul_left (w - 1)).tsum_add hs2, tsum_mul_left, htel, hz]
  ring

lemma zeta1_eq (R : ℝ) (hR : 2 < R) : ∀ w ∈ UR R, riemannZeta₁ w = 1 + Gz w := by
  have hA : AnalyticOnNhd ℂ riemannZeta₁ (UR R) :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd (UR_open R)
  have hB : AnalyticOnNhd ℂ (fun w => 1 + Gz w) (UR R) :=
    ((differentiableOn_const _).add (Gz_diff R)).analyticOnNhd (UR_open R)
  have hconv : Convex ℝ (UR R) := (convex_halfSpace_re_gt _).inter (convex_ball _ _)
  have h2 : (2 : ℂ) ∈ UR R := ⟨by norm_num, by simp; linarith⟩
  have hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] fun w => 1 + Gz w := by
    have hU : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hU] with w hw
    have hw1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    rw [Gz_eq w hw, riemannZeta_eq_inv_sub_mul hw1]
    field_simp
    ring
  intro w hw
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB hconv.isPreconnected h2 hev hw

/-- Polynomial growth of `ζ` for `Re w ≥ 1/2`. -/
lemma zeta_growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 / 2 ≤ w.re → 2 ≤ |w.im| →
    ‖riemannZeta w‖ ≤ C * (1 + ‖w‖) := by
  have hS := summable_rpow_shift (p := 3 / 2) (by norm_num)
  set S := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  refine ⟨1 + S, by positivity, fun w hw him => ?_⟩
  have hw1 : w ≠ 1 := by intro h; rw [h] at him; simp at him; linarith
  have hwm : 2 ≤ ‖w - 1‖ := by
    refine him.trans ?_
    have := Complex.abs_im_le_norm (w - 1)
    simpa using this
  have hmem : w ∈ UR (‖w‖ + 3) := ⟨show (1 / 4 : ℝ) < w.re by linarith, by simp⟩
  have heq := zeta1_eq (‖w‖ + 3) (by linarith [norm_nonneg w]) w hmem
  have hbnd : ∀ n : ℕ, ‖eT w n‖ ≤ ‖w - 1‖ * ‖w‖ * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    intro n
    refine (eT_bound w (by linarith) n).trans ?_
    gcongr
    · have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      exact this
    · linarith
  have hG : ‖Gz w‖ ≤ ‖w - 1‖ * ‖w‖ * S := by
    unfold Gz
    rw [hSdef, ← tsum_mul_left]
    exact tsum_of_norm_bounded (hS.mul_left _).hasSum hbnd
  rw [riemannZeta_eq_inv_sub_mul hw1, heq, norm_mul, norm_inv]
  have hpos : 0 < ‖w - 1‖ := by linarith
  rw [inv_mul_le_iff₀ hpos]
  calc ‖1 + Gz w‖ ≤ 1 + ‖w - 1‖ * ‖w‖ * S := (norm_add_le _ _).trans (by simp [hG])
    _ ≤ ‖w - 1‖ * ((1 + S) * (1 + ‖w‖)) := by
      nlinarith [norm_nonneg w, mul_nonneg (norm_nonneg w) hS0]

end GuthMaynard.CitedZeros.MP23

-- ===== Part B =====

/-! Part B: the cancelled kernel, the contour shift, and the residue bound. -/

open Complex MeasureTheory Filter Topology Set

namespace GuthMaynard.CitedZeros.MP23


/-- `a(n) = ∑_{d ∣ n, d ≤ 𝓜} μ(d)`. -/
noncomputable def aC (T : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
    (ArithmeticFunction.moebius d : ℂ)

/-- `M(s) = ∑_{m ≤ 𝓜} μ(m) m^{-s}`. -/
noncomputable def Mf (T : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)

/-- The dyadic block `D_N(s)`. -/
noncomputable def Db (T : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), (aC T n * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)) * (n : ℂ) ^ (-s)

/-- The terms of `I(ρ)`. -/
noncomputable def bT (T : ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  aC T n * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ) * (n : ℂ) ^ (-ρ)

/-- `I(ρ) = ∑ a(n) n^{-ρ} e^{-n/Y}`. -/
noncomputable def Iser (T : ℝ) (ρ : ℂ) : ℂ := ∑' n : ℕ, bT T ρ n

/-- The integrand `Y^s Γ(s) M(ρ+s) ζ(ρ+s)`. -/
noncomputable def Ff (T : ℝ) (ρ s : ℂ) : ℂ :=
  (T : ℂ) ^ (s / 2) * Complex.Gamma s * Mf T (ρ + s) * riemannZeta (ρ + s)

/-- `(1/2π) ∫ F(x + iu) du`. -/
noncomputable def lineInt (T : ℝ) (ρ : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, Ff T ρ ((x : ℂ) + (u : ℂ) * I)

/-- The residue `Y^{1-ρ} Γ(1-ρ) M(1)`. -/
noncomputable def Res (T : ℝ) (ρ : ℂ) : ℂ :=
  (T : ℂ) ^ ((1 - ρ) / 2) * Complex.Gamma (1 - ρ) * Mf T 1

/-- The integrand with the `Γ` pole at `0` cancelled against `ζ(ρ) = 0`. -/
noncomputable def Ft (T : ℝ) (ρ s : ℂ) : ℂ :=
  (T : ℂ) ^ (s / 2) * Complex.Gamma (s + 1) * dslope (fun w => riemannZeta (ρ + w)) 0 s *
    Mf T (ρ + s)

/-! ### Elementary bounds -/

lemma Mf_bound (T : ℝ) {w : ℂ} (hw : 0 ≤ w.re) : ‖Mf T w‖ ≤ (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) := by
  unfold Mf
  refine (norm_sum_le _ _).trans ?_
  have : ∀ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ ≤ 1 := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [norm_mul]
    have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := m)
      rw [show ((ArithmeticFunction.moebius m : ℤ) : ℂ) = (((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ)
        by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast this
    have h2 : ‖(m : ℂ) ^ (-w)‖ ≤ 1 := by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm1 (by simp; linarith)
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma floorM_le (T : ℝ) (hT : 1 ≤ T) : (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) ≤ 2 * T := by
  refine (Nat.floor_le (by positivity)).trans ?_
  have : T ^ (1 / 100 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  rw [Real.rpow_one] at this
  linarith

lemma norm_Tpow (T : ℝ) (hT : 0 < T) (s : ℂ) : ‖(T : ℂ) ^ (s / 2)‖ = T ^ (s.re / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hT]
  simp

/-! ### The cancelled kernel -/

lemma Ft_eq {T : ℝ} {ρ s : ℂ} (h0 : riemannZeta ρ = 0) (hs : s ≠ 0) : Ft T ρ s = Ff T ρ s := by
  unfold Ft Ff
  rw [dslope_of_ne _ hs, slope_def_field, Complex.Gamma_add_one s hs]
  simp only [add_zero, h0, sub_zero]
  field_simp

lemma Ft_diff {T : ℝ} (hT : 0 < T) {ρ s : ℂ} (hρ : ρ ≠ 1) (hs : -1 < s.re) (hs1 : s ≠ 1 - ρ) :
    DifferentiableAt ℂ (Ft T ρ) s := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have d1 : DifferentiableAt ℂ (fun s : ℂ => (T : ℂ) ^ (s / 2)) s :=
    (differentiableAt_id.div_const 2).const_cpow (Or.inl hT0)
  have d2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s + 1)) s := by
    refine (Complex.differentiableAt_Gamma _ ?_).comp s (differentiableAt_id.add_const 1)
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have d3 : DifferentiableAt ℂ (dslope (fun w => riemannZeta (ρ + w)) 0) s := by
    set V : Set ℂ := {w : ℂ | ρ + w ≠ 1} with hV
    have hVo : IsOpen V := isOpen_ne_fun (continuous_const.add continuous_id) continuous_const
    have h0V : V ∈ 𝓝 (0 : ℂ) := hVo.mem_nhds (by simp [hV, hρ])
    have hd : DifferentiableOn ℂ (fun w => riemannZeta (ρ + w)) V := by
      intro w hw
      exact ((differentiableAt_riemannZeta hw).comp w
        (differentiableAt_const ρ |>.add differentiableAt_id)).differentiableWithinAt
    have := (differentiableOn_dslope h0V).mpr hd
    have hsV : s ∈ V := by
      simp only [hV, mem_setOf_eq]
      intro h; apply hs1; rw [← h]; ring
    exact this.differentiableAt (hVo.mem_nhds hsV)
  have d4 : DifferentiableAt ℂ (fun s : ℂ => Mf T (ρ + s)) s := by
    unfold Mf
    apply DifferentiableAt.fun_sum
    intro m hm
    have hm0 : (m : ℂ) ≠ 0 := by
      have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      exact_mod_cast (by omega : m ≠ 0)
    exact (differentiableAt_const _).mul
      ((differentiableAt_const ρ |>.add differentiableAt_id).neg.const_cpow (Or.inl hm0))
  exact ((d1.mul d2).mul d3).mul d4

lemma Ft_res {T : ℝ} (hT : 0 < T) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (hρ : ρ.re < 1) :
    Tendsto (fun z => (z - (1 - ρ)) * Ft T ρ z) (𝓝[≠] (1 - ρ)) (𝓝 (Res T ρ)) := by
  set s₀ := 1 - ρ with hs₀
  have hs₀re : 0 < s₀.re := by simp [hs₀]; linarith
  have hs₀0 : s₀ ≠ 0 := by intro h; rw [h] at hs₀re; simp at hs₀re
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  -- the regular factor
  set A : ℂ → ℂ := fun z => (T : ℂ) ^ (z / 2) * Complex.Gamma z * Mf T (ρ + z) with hA
  have hAc : ContinuousAt A s₀ := by
    have d1 : DifferentiableAt ℂ (fun s : ℂ => (T : ℂ) ^ (s / 2)) s₀ :=
      (differentiableAt_id.div_const 2).const_cpow (Or.inl hT0)
    have d2 : DifferentiableAt ℂ Complex.Gamma s₀ := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have d4 : DifferentiableAt ℂ (fun s : ℂ => Mf T (ρ + s)) s₀ := by
      unfold Mf
      apply DifferentiableAt.fun_sum
      intro m hm
      have hm0 : (m : ℂ) ≠ 0 := by
        have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        exact_mod_cast (by omega : m ≠ 0)
      exact (differentiableAt_const _).mul
        ((differentiableAt_const ρ |>.add differentiableAt_id).neg.const_cpow (Or.inl hm0))
    exact ((d1.mul d2).mul d4).continuousAt
  have hAlim : Tendsto A (𝓝[≠] s₀) (𝓝 (Res T ρ)) := by
    have := hAc.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
    convert this using 2
    simp only [hA, Res, hs₀]
    congr 2
    ring_nf
  -- the polar factor
  have hmap : Tendsto (fun z : ℂ => ρ + z) (𝓝[≠] s₀) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun z : ℂ => ρ + z) (𝓝 s₀) (𝓝 (ρ + s₀)) :=
        (continuous_const.add continuous_id).tendsto s₀
      rw [show ρ + s₀ = 1 by simp [hs₀]] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h; apply hz; show z = s₀; rw [hs₀]; linear_combination h
  have hZ : Tendsto (fun z : ℂ => (ρ + z - 1) * riemannZeta (ρ + z)) (𝓝[≠] s₀) (𝓝 1) :=
    riemannZeta_residue_one.comp hmap
  have hprod := hAlim.mul hZ
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  have hne0 : ∀ᶠ z in 𝓝[≠] s₀, z ≠ 0 := (eventually_ne_nhds hs₀0).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne0] with z hz
  rw [Ft_eq h0 hz]
  simp only [hA, Ff, hs₀]
  ring

lemma Ft_decay {T : ℝ} (hT : 1 ≤ T) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) :
    ∃ C H : ℝ, ∀ z : ℂ, 1 / 2 - ρ.re ≤ z.re → z.re ≤ 2 → H ≤ |z.im| →
      ‖Ft T ρ z‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C₃, hC₃, hΓ⟩ := gamma_decay (1 / 2) 3 (by norm_num) 3
  obtain ⟨Cz, hCz, hζ⟩ := zeta_growth
  set Mm : ℝ := (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) with hMm
  have hMm0 : 0 ≤ Mm := by positivity
  refine ⟨T * C₃ * Mm * Cz * (3 + ‖ρ‖), |ρ.im| + 3, fun z hz1 hz2 hzi => ?_⟩
  have hT0 : 0 < T := by linarith
  set t := z.im with ht
  have hti : 1 ≤ |t| := by linarith [abs_nonneg ρ.im]
  have hz0 : z ≠ 0 := by
    intro h
    have : t = 0 := by rw [ht, h]; simp
    rw [this] at hti; simp at hti; linarith
  rw [Ft_eq h0 hz0]
  unfold Ff
  rw [norm_mul, norm_mul, norm_mul, norm_Tpow T hT0]
  -- the four factors
  have f1 : T ^ (z.re / 2) ≤ T := by
    calc T ^ (z.re / 2) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = T := Real.rpow_one T
  have hznorm : 1 ≤ ‖z‖ := hti.trans (by rw [ht]; exact Complex.abs_im_le_norm z)
  have f2 : (1 + |t|) ^ 3 * ‖Complex.Gamma z‖ ≤ C₃ := by
    have hg := hΓ (z + 1) (by simp; linarith) (by simp; linarith)
    simp only [add_im, one_im, add_zero] at hg
    have : ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + 1)‖ := by
      rw [Complex.Gamma_add_one z hz0, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hznorm
    calc (1 + |t|) ^ 3 * ‖Complex.Gamma z‖ ≤ (1 + |t|) ^ 3 * ‖Complex.Gamma (z + 1)‖ := by gcongr
      _ ≤ C₃ := hg
  have f3 : ‖Mf T (ρ + z)‖ ≤ Mm := Mf_bound T (by simp; linarith)
  have f4 : ‖riemannZeta (ρ + z)‖ ≤ Cz * ((3 + ‖ρ‖) * (1 + |t|)) := by
    have hw1 : 1 / 2 ≤ (ρ + z).re := by simp; linarith
    have hw2 : 2 ≤ |(ρ + z).im| := by
      simp only [add_im]
      have := abs_sub_abs_le_abs_sub z.im (-ρ.im)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      rw [← ht] at this ⊢
      linarith
    refine (hζ _ hw1 hw2).trans ?_
    gcongr
    have hzn : ‖z‖ ≤ 2 + |t| := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 2 + |t| := by
          rw [← ht]; gcongr; rw [abs_le]; constructor <;> linarith
    have := norm_add_le ρ z
    nlinarith [norm_nonneg ρ, abs_nonneg t]
  have hA : 0 < 1 + |t| := by positivity
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  rw [le_div_iff₀ (by positivity)]
  have hG : ‖Complex.Gamma z‖ ≤ C₃ / (1 + |t|) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc T ^ (z.re / 2) * ‖Complex.Gamma z‖ * ‖Mf T (ρ + z)‖ * ‖riemannZeta (ρ + z)‖ * (1 + t ^ 2)
      ≤ T * (C₃ / (1 + |t|) ^ 3) * Mm * (Cz * ((3 + ‖ρ‖) * (1 + |t|))) * (1 + |t|) ^ 2 := by
        gcongr
    _ = T * C₃ * Mm * Cz * (3 + ‖ρ‖) := by
        field_simp

/-! ### The reference function `Γ(s - s₀)` -/

lemma g_decay {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ∃ C H : ℝ, ∀ z : ℂ, 1 / 2 - ρ.re ≤ z.re → z.re ≤ 2 → H ≤ |z.im| →
      ‖Complex.Gamma (z - (1 - ρ))‖ ≤ C / (1 + z.im ^ 2) := by
  obtain ⟨C₂, hC₂, hΓ⟩ := gamma_decay (1 / 2) 3 (by norm_num) 2
  refine ⟨4 * C₂, 2 * |ρ.im| + 2, fun z hz1 hz2 hzi => ?_⟩
  set w := z - (1 - ρ) with hw
  have hwim : w.im = z.im + ρ.im := by simp [hw]
  have hwre : w.re = z.re - 1 + ρ.re := by simp [hw]; ring
  have hwi : |z.im| / 2 + 1 ≤ |w.im| := by
    rw [hwim]
    have := abs_sub_abs_le_abs_sub z.im (-ρ.im)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hwi; simp at hwi; linarith [abs_nonneg z.im]
  have hwn : 1 ≤ ‖w‖ := le_trans (by linarith [abs_nonneg z.im]) (hwi.trans (Complex.abs_im_le_norm w))
  have hg := hΓ (w + 1) (by simp; linarith) (by simp; linarith)
  simp only [add_im, one_im, add_zero] at hg
  have h1 : ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + 1)‖ := by
    rw [Complex.Gamma_add_one w hw0, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hwn
  have hsq : 1 + z.im ^ 2 ≤ 4 * (1 + |w.im|) ^ 2 := by
    nlinarith [sq_abs z.im, abs_nonneg z.im, abs_nonneg w.im]
  rw [le_div_iff₀ (by positivity)]
  calc ‖Complex.Gamma w‖ * (1 + z.im ^ 2) ≤ ‖Complex.Gamma (w + 1)‖ * (4 * (1 + |w.im|) ^ 2) := by
        gcongr
    _ = 4 * ((1 + |w.im|) ^ 2 * ‖Complex.Gamma (w + 1)‖) := by ring
    _ ≤ 4 * C₂ := by gcongr

lemma g_res (s₀ : ℂ) :
    Tendsto (fun z => (z - s₀) * Complex.Gamma (z - s₀)) (𝓝[≠] s₀) (𝓝 1) := by
  have hc : ContinuousAt (fun z : ℂ => Complex.Gamma (z - s₀ + 1)) s₀ := by
    refine ((Complex.differentiableAt_Gamma _ ?_).comp s₀
      ((differentiableAt_id.sub_const s₀).add_const 1)).continuousAt
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
  simp only [sub_self, zero_add, Complex.Gamma_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [Complex.Gamma_add_one _ (sub_ne_zero.mpr hz)]

lemma g_diff {ρ : ℂ} (z : ℂ) (hz1 : 1 / 2 - ρ.re ≤ z.re) (hz : z ≠ 1 - ρ) :
    DifferentiableAt ℂ (fun z => Complex.Gamma (z - (1 - ρ))) z := by
  refine (Complex.differentiableAt_Gamma _ ?_).comp z (differentiableAt_id.sub_const _)
  intro m hm
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; apply hz; simpa [sub_eq_zero] using hm
  · have := congrArg Complex.re hm
    simp at this
    have : (1 : ℝ) ≤ m := by exact_mod_cast h
    linarith

/-! ### The contour shift -/

lemma ae_ne_zero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
  rw [MeasureTheory.ae_iff]; simp

lemma line_eq (T : ℝ) {ρ : ℂ} (h0 : riemannZeta ρ = 0) (x : ℝ) :
    (∫ u : ℝ, Ff T ρ ((x : ℂ) + (u : ℂ) * I)) = ∫ u : ℝ, Ft T ρ ((x : ℂ) + (u : ℂ) * I) := by
  apply integral_congr_ae
  filter_upwards [ae_ne_zero] with u hu
  rw [Ft_eq h0]
  intro h
  apply hu
  have := congrArg Complex.im h
  simpa using this

lemma g_line (s₀ : ℂ) (x : ℝ) :
    (∫ u : ℝ, Complex.Gamma ((x : ℂ) + (u : ℂ) * I - s₀)) =
      ∫ u : ℝ, Complex.Gamma (((x - s₀.re : ℝ) : ℂ) + (u : ℂ) * I) := by
  have := MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun u : ℝ => Complex.Gamma (((x - s₀.re : ℝ) : ℂ) + (u : ℂ) * I)) s₀.im
  rw [← this]
  congr 1
  funext u
  congr 1
  apply Complex.ext <;> simp

/-- The contour shift from `Re s = 2` to `Re s = 1/2 - β`. -/
lemma contour_shift : ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 1 ≤ T → ∀ ρ : ℂ, riemannZeta ρ = 0 →
    0 < ρ.re → ρ.re < 1 → 1 ≤ ρ.im →
    ‖lineInt T ρ (1 / 2 - ρ.re) - lineInt T ρ 2‖ ≤ K * ‖Res T ρ‖ := by
  obtain ⟨K₀, hK₀, hK⟩ := gamma_line_bound
  refine ⟨K₀ / Real.pi, by positivity, fun T hT ρ h0 hρ0 hρ1 hγ => ?_⟩
  have hT0 : 0 < T := by linarith
  have hρ1' : ρ ≠ 1 := by intro h; rw [h] at hρ1; simp at hρ1
  have hshift := shift_pole (Ft T ρ) (fun z => Complex.Gamma (z - (1 - ρ))) (1 / 2 - ρ.re) 2
    (1 - ρ) (Res T ρ) (by simp; linarith) (by simp; linarith)
    (fun z h1 _ h3 => Ft_diff hT0 hρ1' (by linarith) h3)
    (fun z h1 _ h3 => g_diff z h1 h3)
    (Ft_res hT0 h0 hρ1) (g_res (1 - ρ)) (Ft_decay hT h0 hρ0 hρ1) (g_decay hρ0 hρ1)
  unfold lineInt
  rw [line_eq T h0, line_eq T h0, ← mul_sub]
  push_cast at hshift ⊢
  rw [hshift]
  have e1 := g_line (1 - ρ) (1 / 2 - ρ.re)
  have e2 := g_line (1 - ρ) 2
  push_cast at e1 e2
  rw [e1, e2]
  have b1 := hK ((1 / 2 - ρ.re) - (1 - ρ).re) (Or.inl (by simp; ring))
  have b2 := hK (2 - (1 - ρ).re) (Or.inr ⟨by simp; linarith, by simp; linarith⟩)
  push_cast at b1 b2
  rw [norm_mul, norm_mul]
  have hpi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  have hsub := norm_sub_le (∫ u : ℝ, Complex.Gamma (((1 / 2 - ρ.re - (1 - ρ).re : ℝ) : ℂ) + (u : ℂ) * I))
    (∫ u : ℝ, Complex.Gamma (((2 - (1 - ρ).re : ℝ) : ℂ) + (u : ℂ) * I))
  push_cast at hsub
  have hRn := norm_nonneg (Res T ρ)
  calc 1 / (2 * Real.pi) * (‖Res T ρ‖ * ‖_ - _‖)
      ≤ 1 / (2 * Real.pi) * (‖Res T ρ‖ * (K₀ + K₀)) := by gcongr; linarith
    _ = K₀ / Real.pi * ‖Res T ρ‖ := by field_simp; ring

/-- The residue term is negligible. -/
lemma res_small (ε : ℝ) (hε : 0 < ε) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ ρ : ℂ, 0 < ρ.re →
    ρ.re < 1 → T ≤ ρ.im → ‖Res T ρ‖ ≤ ε := by
  obtain ⟨C₄, hC₄, hΓ⟩ := gamma_decay (1 / 2) 3 (by norm_num) 4
  refine ⟨max 1 (2 * C₄ / ε), fun T hT ρ hρ0 hρ1 hγ => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTε : 2 * C₄ / ε ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  unfold Res
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT0]
  have f1 : T ^ (((1 - ρ) / 2).re) ≤ T := by
    calc T ^ (((1 - ρ) / 2).re) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by simp; linarith)
      _ = T := Real.rpow_one T
  have f3 : ‖Mf T 1‖ ≤ 2 * T := (Mf_bound T (by simp)).trans (floorM_le T hT1)
  have hs : (1 - ρ) ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsn : T ≤ ‖1 - ρ‖ := by
    refine hγ.trans ?_
    have := Complex.abs_im_le_norm (1 - ρ)
    simp at this
    exact (le_abs_self _).trans this
  have hg := hΓ (1 - ρ + 1) (by simp; linarith) (by simp; linarith)
  simp only [add_im, sub_im, one_im, zero_sub, add_zero, abs_neg] at hg
  have hγ' : T ≤ |ρ.im| := hγ.trans (le_abs_self _)
  have f2 : ‖Complex.Gamma (1 - ρ)‖ * T ^ 4 ≤ C₄ := by
    have e : ‖Complex.Gamma (1 - ρ + 1)‖ = ‖1 - ρ‖ * ‖Complex.Gamma (1 - ρ)‖ := by
      rw [Complex.Gamma_add_one _ hs, norm_mul]
    rw [e] at hg
    have h4 : T ^ 4 ≤ (1 + |ρ.im|) ^ 4 * ‖1 - ρ‖ := by
      have : T ^ 4 ≤ (1 + |ρ.im|) ^ 4 := by gcongr; linarith
      exact this.trans (le_mul_of_one_le_right (by positivity) (by linarith))
    have hGn := norm_nonneg (Complex.Gamma (1 - ρ))
    calc ‖Complex.Gamma (1 - ρ)‖ * T ^ 4 ≤ ‖Complex.Gamma (1 - ρ)‖ * ((1 + |ρ.im|) ^ 4 * ‖1 - ρ‖) := by
          gcongr
      _ = (1 + |ρ.im|) ^ 4 * (‖1 - ρ‖ * ‖Complex.Gamma (1 - ρ)‖) := by ring
      _ ≤ C₄ := hg
  have hGn := norm_nonneg (Complex.Gamma (1 - ρ))
  have hG : ‖Complex.Gamma (1 - ρ)‖ ≤ C₄ / T ^ 4 := by
    rw [le_div_iff₀ (by positivity)]; exact f2
  calc T ^ (((1 - ρ) / 2).re) * ‖Complex.Gamma (1 - ρ)‖ * ‖Mf T 1‖ ≤ T * (C₄ / T ^ 4) * (2 * T) := by
        gcongr
    _ = 2 * C₄ / T ^ 2 := by field_simp
    _ ≤ 2 * C₄ / T := by
        apply div_le_div_of_nonneg_left (by positivity) hT0
        nlinarith
    _ ≤ ε := by
        rw [div_le_iff₀ hT0]
        rw [div_le_iff₀ hε] at hTε
        linarith

end GuthMaynard.CitedZeros.MP23

-- ===== Part C =====

/-! Part C: Mellin inversion on the line `Re s = 2`. -/

open Complex MeasureTheory Filter Topology Set

namespace GuthMaynard.CitedZeros.MP23


lemma moeb_norm_le (m : ℕ) : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
  have := ArithmeticFunction.abs_moebius_le_one (n := m)
  rw [show ((ArithmeticFunction.moebius m : ℤ) : ℂ) = (((ArithmeticFunction.moebius m : ℤ) : ℝ) : ℂ)
    by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast this

lemma aC_norm_le (T : ℝ) (n : ℕ) : ‖aC T n‖ ≤ n := by
  unfold aC
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (fun m _ => moeb_norm_le m)).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self n)

/-- The Dirichlet series of `a(n)` is `M(w) ζ(w)`. -/
lemma dirichlet_aC (T : ℝ) {w : ℂ} (hw : 1 < w.re) :
    ∑' n : ℕ, aC T n * (n : ℂ) ^ (-w) = Mf T w * riemannZeta w := by
  set N := ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ with hN
  set f : ℕ → ℂ := fun m => if 1 ≤ m ∧ m ≤ N then (ArithmeticFunction.moebius m : ℂ) else 0 with hf
  have hfs : LSeriesSummable f w := by
    unfold LSeriesSummable
    apply summable_of_ne_finset_zero (s := Finset.Icc 1 N)
    intro m hm
    rw [LSeries.term_def]
    simp only [Finset.mem_Icc] at hm
    simp [hf, hm]
  have h1s : LSeriesSummable 1 w := LSeriesSummable_one_iff.mpr hw
  have hconv := LSeries_convolution' hfs h1s
  rw [LSeries_one_eq_riemannZeta hw] at hconv
  have hLf : LSeries f w = Mf T w := by
    unfold LSeries Mf
    rw [tsum_eq_sum (s := Finset.Icc 1 N)]
    · apply Finset.sum_congr rfl
      intro m hm
      have hm' := Finset.mem_Icc.mp hm
      rw [LSeries.term_def, if_neg (by omega), hf]
      simp only [hm', and_self, if_true]
      rw [Complex.cpow_neg, div_eq_mul_inv]
    · intro m hm
      rw [LSeries.term_def]
      simp only [Finset.mem_Icc] at hm
      simp [hf, hm]
  rw [hLf] at hconv
  rw [← hconv]
  unfold LSeries
  congr 1
  funext n
  rw [LSeries.term_def, LSeries.convolution_def]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aC]
  rw [if_neg hn.ne', Complex.cpow_neg, div_eq_mul_inv]
  congr 1
  show aC T n = ∑ p ∈ n.divisorsAntidiagonal, f p.1 * (1 : ℕ → ℂ) p.2
  rw [Nat.sum_divisorsAntidiagonal (fun a b => f a * (1 : ℕ → ℂ) b)]
  unfold aC
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  simp only [Pi.one_apply, mul_one, hf]
  have : (d ≤ N) ↔ ((d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)) := by
    rw [hN]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have h0 : 0 ≤ 2 * T ^ (1 / 100 : ℝ) := by
        by_contra h0; push Not at h0
        have : ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega
      have := (Nat.floor_le h0)
      have : (d : ℝ) ≤ ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ := by exact_mod_cast h
      linarith
    · intro h
      exact Nat.le_floor h
  by_cases hdN : d ≤ N
  · rw [if_pos (this.mp hdN), if_pos ⟨hd1, hdN⟩]
  · rw [if_neg (fun h => hdN (this.mpr h)), if_neg (fun h => hdN h.2)]

/-- `mellin (e^{-x}) = Γ`. -/
lemma mellin_exp {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs]
  unfold mellin Complex.GammaIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  simp only [smul_eq_mul]
  ring

lemma gamma_line_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun u : ℝ => Complex.Gamma ((c : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨C, _, h⟩ := gamma_sq_decay c c hc
  refine line_integrable Complex.Gamma c C (fun u => ?_) (fun u => ?_)
  · apply (Complex.differentiableAt_Gamma _ _).continuousAt
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  · simpa using h ((c : ℂ) + (u : ℂ) * I) (by simp) (by simp)

/-- Cahen–Mellin: `(1/2π) ∫ Γ(c+iu) x^{-(c+iu)} du = e^{-x}`. -/
lemma cahen_mellin (c : ℝ) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, (x : ℂ) ^ (-((c : ℂ) + (u : ℂ) * I)) *
      Complex.Gamma ((c : ℂ) + (u : ℂ) * I) = (Real.exp (-x) : ℂ) := by
  have hconv : MellinConvergent (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) (c : ℂ) := by
    unfold MellinConvergent
    have := Complex.GammaIntegral_convergent (s := (c : ℂ)) (by simpa using hc)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  have hvert : VerticalIntegrable (mellin (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ))) c := by
    unfold VerticalIntegrable
    refine (gamma_line_integrable c hc).congr (ae_of_all _ (fun u => ?_))
    simp only
    rw [mellin_exp (by simpa using hc)]
  have hcont : ContinuousAt (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) x := by fun_prop
  have := mellinInv_mellin_eq c _ hx hconv hvert hcont
  unfold mellinInv at this
  rw [← this, Complex.real_smul]
  push_cast
  congr 1
  apply integral_congr_ae
  refine ae_of_all _ (fun u => ?_)
  have hm := mellin_exp (s := (c : ℂ) + (u : ℂ) * I) (by simp [hc])
  push_cast at hm
  simp only [smul_eq_mul]
  rw [hm]

/-- The Mellin kernel `x^{-(2+iu)} Γ(2+iu)`. -/
noncomputable def Kx (x : ℝ) (u : ℝ) : ℂ :=
  (x : ℂ) ^ (-((2 : ℝ) + (u : ℂ) * I)) * Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)

lemma Kx_norm {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖Kx x u‖ = x ^ (-(2 : ℝ)) * ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  unfold Kx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma Kx_integrable {x : ℝ} (hx : 0 < x) : Integrable (Kx x) := by
  have hG := gamma_line_integrable 2 (by norm_num)
  have hc : Continuous (Kx x) := by
    unfold Kx
    apply Continuous.mul
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
    · rw [continuous_iff_continuousAt]
      intro u
      apply ContinuousAt.comp (g := Complex.Gamma) _ (by fun_prop)
      apply (Complex.differentiableAt_Gamma _ _).continuousAt
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  refine (hG.norm.const_mul (x ^ (-(2 : ℝ)))).mono' hc.aestronglyMeasurable
    (ae_of_all _ (fun u => ?_))
  rw [Kx_norm hx]

lemma Kx_integral {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, Kx x u = (Real.exp (-x) : ℂ) := by
  have := cahen_mellin 2 (by norm_num) hx
  rw [← this]
  rfl

lemma cpow_split {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) (ρ s : ℂ) :
    (T : ℂ) ^ (s / 2) * (n : ℂ) ^ (-(ρ + s)) =
      (n : ℂ) ^ (-ρ) * (((n : ℝ) / T ^ (1 / 2 : ℝ) : ℝ) : ℂ) ^ (-s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hY : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
  have hx : (0 : ℝ) < (n : ℝ) / T ^ (1 / 2 : ℝ) := div_pos hn' hY
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx0 : (((n : ℝ) / T ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hT0, Complex.cpow_def_of_ne_zero hn0,
    Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hx0, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hT.le,
    show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log hn'.le,
    Real.log_div hn'.ne' hY.ne', Real.log_rpow hT]
  push_cast
  ring

/-- Mellin inversion on `Re s = 2`. -/
lemma mellin_line {T : ℝ} (hT : 1 ≤ T) {ρ : ℂ} (hρ : 0 < ρ.re) : lineInt T ρ 2 = Iser T ρ := by
  have hT0 : 0 < T := by linarith
  set Y : ℝ := T ^ (1 / 2 : ℝ) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hT0 _
  set c : ℕ → ℂ := fun n => aC T n * (n : ℂ) ^ (-ρ) with hc
  set x : ℕ → ℝ := fun n => (n : ℝ) / Y with hx
  have hc0 : c 0 = 0 := by simp [hc, aC]
  -- pointwise expansion
  have hpt : ∀ u : ℝ, Ff T ρ (((2 : ℝ) : ℂ) + (u : ℂ) * I) = ∑' n : ℕ, c n * Kx (x n) u := by
    intro u
    set s : ℂ := ((2 : ℝ) : ℂ) + (u : ℂ) * I with hs
    have hre : 1 < (ρ + s).re := by simp [hs]; linarith
    unfold Ff
    rw [mul_assoc _ (Mf T (ρ + s)), ← dirichlet_aC T hre, ← tsum_mul_left]
    congr 1
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0, aC]
    simp only [hc, hx, Kx]
    have := cpow_split hT0 hn ρ s
    rw [← hs]
    calc (T : ℂ) ^ (s / 2) * Complex.Gamma s * (aC T n * (n : ℂ) ^ (-(ρ + s)))
        = aC T n * Complex.Gamma s * ((T : ℂ) ^ (s / 2) * (n : ℂ) ^ (-(ρ + s))) := by ring
      _ = _ := by rw [this]; ring
  -- integrability and summability
  have hint : ∀ n : ℕ, Integrable (fun u : ℝ => c n * Kx (x n) u) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]
    exact (Kx_integrable (div_pos (by exact_mod_cast hn) hY)).const_mul _
  set G : ℝ := ∫ u : ℝ, ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ with hG
  have hG0 : 0 ≤ G := integral_nonneg (fun _ => norm_nonneg _)
  have hnorm : ∀ n : ℕ, ∫ u : ℝ, ‖c n * Kx (x n) u‖ ≤ Y ^ 2 * G * (n : ℝ) ^ (-1 - ρ.re) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]; positivity
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hxn : 0 < x n := div_pos hn' hY
    have e : (fun u : ℝ => ‖c n * Kx (x n) u‖) =
        fun u : ℝ => (‖c n‖ * x n ^ (-(2 : ℝ))) * ‖Complex.Gamma (((2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
      funext u; rw [norm_mul, Kx_norm hxn]; ring
    rw [e, integral_const_mul]
    have hcn : ‖c n‖ ≤ (n : ℝ) * (n : ℝ) ^ (-ρ.re) := by
      simp only [hc]
      rw [norm_mul, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hn']
      simp only [neg_re]
      gcongr
      exact aC_norm_le T n
    have hxp : x n ^ (-(2 : ℝ)) = Y ^ 2 * (n : ℝ) ^ (-(2 : ℝ)) := by
      simp only [hx]
      rw [Real.div_rpow hn'.le hY.le, Real.rpow_neg hY.le, Real.rpow_neg hn'.le,
        Real.rpow_two, Real.rpow_two]
      field_simp
    calc ‖c n‖ * x n ^ (-(2 : ℝ)) * G ≤ ((n : ℝ) * (n : ℝ) ^ (-ρ.re)) * x n ^ (-(2 : ℝ)) * G := by
          gcongr
      _ = Y ^ 2 * G * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-ρ.re) * (n : ℝ) ^ (-(2 : ℝ))) := by
          rw [hxp, Real.rpow_one]; ring
      _ = Y ^ 2 * G * (n : ℝ) ^ (-1 - ρ.re) := by
          rw [← Real.rpow_add hn', ← Real.rpow_add hn']; ring_nf
  have hsum : Summable (fun n : ℕ => ∫ u : ℝ, ‖c n * Kx (x n) u‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) hnorm ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hfub := integral_tsum_of_summable_integral_norm hint hsum
  unfold lineInt Iser
  rw [show (fun u : ℝ => Ff T ρ (((2 : ℝ) : ℂ) + (u : ℂ) * I)) =
    fun u => ∑' n : ℕ, c n * Kx (x n) u from funext hpt]
  push_cast at hfub ⊢
  rw [← hfub, ← tsum_mul_left]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hc0, bT, aC]
  have hxn : 0 < x n := div_pos (by exact_mod_cast hn) hY
  rw [integral_const_mul]
  calc (1 / (2 * (Real.pi : ℂ))) * (c n * ∫ u : ℝ, Kx (x n) u)
      = c n * ((1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, Kx (x n) u) := by push_cast; ring
    _ = c n * (Real.exp (-x n) : ℂ) := by rw [Kx_integral hxn]
    _ = bT T ρ n := by
        simp only [hc, hx, bT, hYdef, neg_div]
        ring

end GuthMaynard.CitedZeros.MP23

-- ===== Part D =====

/-! Part D: the dyadic decomposition of `I(ρ)`. -/

open Complex MeasureTheory Filter Topology Set

namespace GuthMaynard.CitedZeros.MP23


lemma block_sum (b : ℕ → ℂ) (K : ℕ) :
    ∑ n ∈ Finset.range (2 ^ K + 1), b n =
      b 0 + b 1 + ∑ j ∈ Finset.range K, ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), b n := by
  induction K with
  | zero => simp [Finset.sum_range_succ]
  | succ K ih =>
    rw [Finset.sum_range_succ (fun j => ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), b n) K, ← add_assoc,
      ← ih, ← Finset.Ico_add_one_add_one_eq_Ioc, show 2 * 2 ^ K + 1 = 2 ^ (K + 1) + 1 by ring,
      Finset.sum_range_add_sum_Ico _ (by rw [pow_succ]; omega)]

lemma Db_eq (T : ℝ) (N : ℕ) (ρ : ℂ) : Db T N ρ = ∑ n ∈ Finset.Ioc N (2 * N), bT T ρ n := rfl

lemma aC_one (T : ℝ) (_hT : 0 ≤ T) (h : 1 ≤ 2 * T ^ (1 / 100 : ℝ)) : aC T 1 = 1 := by
  unfold aC
  rw [Nat.divisors_one, Finset.filter_singleton, if_pos (by simpa using h)]
  simp

lemma aC_zero_of {T : ℝ} {n : ℕ} (hn : 2 ≤ n) (hnM : (n : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)) :
    aC T n = 0 := by
  unfold aC
  rw [Finset.filter_true_of_mem]
  · have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne (by omega)] at h
    exact_mod_cast h
  · intro d hd
    have := Nat.divisor_le hd
    have : (d : ℝ) ≤ n := by exact_mod_cast this
    linarith

lemma bT_norm_le (T : ℝ) {ρ : ℂ} (hρ : 0 ≤ ρ.re) (n : ℕ) :
    ‖bT T ρ n‖ ≤ (n : ℝ) * Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bT, aC]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold bT
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hn']
  have h1 : (n : ℝ) ^ (-ρ).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp; linarith)
  have h2 := aC_norm_le T n
  calc ‖aC T n‖ * Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) * (n : ℝ) ^ (-ρ).re
      ≤ (n : ℝ) * Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) * 1 := by gcongr
    _ = _ := by ring

/-- Geometric tail estimate. -/
lemma tail_est {Y X : ℝ} (hY : 1 ≤ Y) (hX : 0 ≤ X) (k : ℕ) (hk : X ≤ k) :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ i, (((i + k : ℕ) : ℝ) * Real.exp (-((i + k : ℕ) : ℝ) / Y)) ≤ g i) ∧
      ∑' i, g i ≤ Real.exp (-X / (2 * Y)) * (2 * Y + 1) ^ 2 := by
  have hY0 : 0 < Y := by linarith
  set q : ℝ := Real.exp (-1 / (2 * Y)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    have : Real.exp (-1 / (2 * Y)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) (by linarith))
    rw [Real.exp_zero] at this; exact this
  have hqn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hqpow : ∀ m : ℕ, q ^ m = Real.exp (-(m : ℝ) / (2 * Y)) := by
    intro m; rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  set c : ℝ := Real.exp (-X / (2 * Y)) with hc
  refine ⟨fun i => c * (((i + k : ℕ) : ℝ) * q ^ (i + k)), ?_, ?_, ?_⟩
  · have hs := summable_pow_mul_geometric_of_norm_lt_one 1 hqn
    simp only [pow_one] at hs
    exact ((summable_nat_add_iff k).mpr hs).mul_left c
  · intro i
    set m := i + k with hm
    have hmk : X ≤ (m : ℝ) := by rw [hm]; push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have e : Real.exp (-(m : ℝ) / Y) = Real.exp (-(m : ℝ) / (2 * Y)) * Real.exp (-(m : ℝ) / (2 * Y)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    show (m : ℝ) * Real.exp (-(m : ℝ) / Y) ≤ c * ((m : ℝ) * q ^ m)
    rw [e, hqpow]
    have hle : Real.exp (-(m : ℝ) / (2 * Y)) ≤ c := by
      rw [hc, Real.exp_le_exp]
      apply div_le_div_of_nonneg_right _ (by linarith); linarith
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    calc (m : ℝ) * (Real.exp (-(m : ℝ) / (2 * Y)) * Real.exp (-(m : ℝ) / (2 * Y)))
        = Real.exp (-(m : ℝ) / (2 * Y)) * ((m : ℝ) * Real.exp (-(m : ℝ) / (2 * Y))) := by ring
      _ ≤ c * ((m : ℝ) * Real.exp (-(m : ℝ) / (2 * Y))) := by gcongr
  · rw [tsum_mul_left]
    have hc0 : 0 ≤ c := (Real.exp_pos _).le
    have hs := summable_pow_mul_geometric_of_norm_lt_one 1 hqn
    simp only [pow_one] at hs
    have hshift : ∑' i, (((i + k : ℕ) : ℝ) * q ^ (i + k)) ≤ ∑' m : ℕ, (m : ℝ) * q ^ m := by
      rw [← hs.sum_add_tsum_nat_add k]
      have : 0 ≤ ∑ i ∈ Finset.range k, (i : ℝ) * q ^ i :=
        Finset.sum_nonneg (fun i _ => by positivity)
      push_cast
      linarith
    have hgeo := tsum_coe_mul_geometric_of_norm_lt_one hqn
    have h1q : 1 / (2 * Y + 1) ≤ 1 - q := by
      have hexp := Real.add_one_le_exp (1 / (2 * Y))
      have hqe : q * Real.exp (1 / (2 * Y)) = 1 := by
        rw [hq, ← Real.exp_add]; simp [neg_div]
      have : q * (1 / (2 * Y) + 1) ≤ 1 := by
        calc q * (1 / (2 * Y) + 1) ≤ q * Real.exp (1 / (2 * Y)) := by gcongr
          _ = 1 := hqe
      have e2 : q * (1 / (2 * Y) + 1) = q * (2 * Y + 1) / (2 * Y) := by field_simp; ring
      rw [e2, div_le_one (by linarith)] at this
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hgeo_le : q / (1 - q) ^ 2 ≤ (2 * Y + 1) ^ 2 := by
      have hpos : 0 < 1 - q := by linarith
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ (2 * Y + 1) * (1 - q) := by
        rw [div_le_iff₀ (by linarith)] at h1q; linarith
      nlinarith
    calc c * ∑' i, (((i + k : ℕ) : ℝ) * q ^ (i + k)) ≤ c * ∑' m : ℕ, (m : ℝ) * q ^ m := by gcongr
      _ = c * (q / (1 - q) ^ 2) := by rw [hgeo]
      _ ≤ c * (2 * Y + 1) ^ 2 := by gcongr

/-- Numerical facts for large `T`. -/
lemma log_facts {L : ℝ} (hL : 1000000 ≤ L) :
    2 * Real.log L + Real.log 2 ≤ 9 / 1000 * L := by
  have hL0 : 0 ≤ L := by linarith
  have h1 := Real.log_le_rpow_div hL0 (by norm_num : (0 : ℝ) < 1 / 2)
  set r := L ^ (1 / 2 : ℝ) with hr
  have hr2 : r * r = L := by
    rw [hr, ← Real.rpow_add' hL0 (by norm_num)]; norm_num
  have hr0 : 0 ≤ r := by positivity
  have hr1000 : 1000 ≤ r := by nlinarith
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have : Real.log L ≤ 2 * r := by
    calc Real.log L ≤ r / (1 / 2) := h1
      _ = 2 * r := by ring
  nlinarith

/-- Dyadic decomposition of `I(ρ)`. -/
lemma dyadic_split : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ ρ : ℂ, 0 < ρ.re →
    ∃ S : Finset ℕ, (S.card : ℝ) ≤ 72 / 100 * Real.log T ∧
      (∀ j ∈ S, (2 : ℝ) ^ j ∈ Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2)) ∧
      ‖Iser T ρ - (Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ) - ∑ j ∈ S, Db T (2 ^ j) ρ‖ ≤ 1 / 100 := by
  refine ⟨Real.exp 1000000, fun T hT ρ hρ => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  set L := Real.log T with hLdef
  have hL : 1000000 ≤ L := by rw [hLdef, ← Real.log_exp 1000000]; exact Real.log_le_log (Real.exp_pos _) hT
  have hTL : T = Real.exp L := (Real.exp_log hT0).symm
  set Y : ℝ := T ^ (1 / 2 : ℝ) with hYdef
  have hYL : Y = Real.exp (L / 2) := by
    rw [hYdef, hTL, ← Real.exp_mul]; ring_nf
  have hY1 : 1 ≤ Y := by rw [hYL]; exact Real.one_le_exp (by linarith)
  have hYsq : Y ^ 2 = T := by
    rw [hYL, hTL, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  set X : ℝ := Y * L ^ 2 with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]; nlinarith [sq_nonneg L]
  set F : ℕ := ⌊X⌋₊ with hF
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hX1)
  have hFX : (F : ℝ) ≤ X := Nat.floor_le (by linarith)
  set K : ℕ := Nat.log 2 F + 1 with hK
  have hXK : X < ((2 ^ K : ℕ) : ℝ) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) F
    have h2 : F + 1 ≤ 2 ^ K := this
    have h3 : X < (F : ℝ) + 1 := Nat.lt_floor_add_one X
    have h4 : ((F + 1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h4 ⊢
    linarith
  set P : ℝ := T ^ (1 / 100 : ℝ) with hPdef
  set S : Finset ℕ := (Finset.range K).filter (fun j => P ≤ (2 : ℝ) ^ j) with hS
  have hPL : P = Real.exp (L / 100) := by
    rw [hPdef, hTL, ← Real.exp_mul]; ring_nf
  refine ⟨S, ?_, ?_, ?_⟩
  · -- counting
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set j₀ : ℕ := ⌈(L / 100) / Real.log 2⌉₊ with hj₀
    have hsub : S ⊆ Finset.Ico j₀ K := by
      intro j hj
      rw [hS, Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_Ico]
      refine ⟨?_, hj.1⟩
      apply Nat.ceil_le.mpr
      rw [div_le_iff₀ hlog2]
      have h := Real.log_le_log (by rw [hPL]; exact Real.exp_pos _) hj.2
      rw [hPL, Real.log_exp, Real.log_pow] at h
      linarith
    have hcard : (S.card : ℝ) ≤ (K : ℝ) - (L / 100) / Real.log 2 := by
      have h1 : S.card ≤ K - j₀ := (Finset.card_le_card hsub).trans (by rw [Nat.card_Ico])
      have h2 : (L / 100) / Real.log 2 ≤ (j₀ : ℝ) := Nat.le_ceil _
      rcases le_or_gt j₀ K with h | h
      · have : ((K - j₀ : ℕ) : ℝ) = K - j₀ := by push_cast [Nat.cast_sub h]; ring
        have h3 : (S.card : ℝ) ≤ ((K - j₀ : ℕ) : ℝ) := by exact_mod_cast h1
        linarith
      · have : K - j₀ = 0 := by omega
        rw [this] at h1
        have : S.card = 0 := by omega
        rw [this]
        have : (K : ℝ) < j₀ := by exact_mod_cast h
        push_cast
        -- K ≥ 1 > ... need `(L/100)/log 2 ≤ K` : false in general; use j₀ ≤ ... bound instead
        have hK1 : (L / 100) / Real.log 2 ≤ (K : ℝ) := by
          -- every power `2^j` with `j < K` ... use `2^(K) > X ≥ P`
          have hPX : P ≤ X := by
            rw [hPL, hXdef, hYL]
            have : Real.exp (L / 100) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith)
            have hL2 : 1 ≤ L ^ 2 := by nlinarith
            exact this.trans (le_mul_of_one_le_right (Real.exp_pos _).le hL2)
          have h5 : P < (2 : ℝ) ^ K := by
            have := hXK; push_cast at this; linarith
          have h6 := Real.log_lt_log (by rw [hPL]; exact Real.exp_pos _) h5
          rw [hPL, Real.log_exp, Real.log_pow] at h6
          rw [div_le_iff₀ hlog2]; linarith
        linarith
    have hKle : (K : ℝ) ≤ Real.log X / Real.log 2 + 1 := by
      have h1 : 2 ^ (Nat.log 2 F) ≤ F := Nat.pow_log_le_self 2 (by omega)
      have h2 : ((2 : ℝ) ^ (Nat.log 2 F)) ≤ X := by
        have : ((2 ^ (Nat.log 2 F) : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast h1
        push_cast at this; linarith
      have h3 := Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at h3
      rw [hK]; push_cast
      have : (Nat.log 2 F : ℝ) ≤ Real.log X / Real.log 2 := by
        rw [le_div_iff₀ hlog2]; linarith
      linarith
    have hlogX : Real.log X = L / 2 + 2 * Real.log L := by
      rw [hXdef, Real.log_mul (by positivity) (by positivity), hYL, Real.log_exp, Real.log_pow]
      push_cast; ring
    have hnum := log_facts hL
    have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    rw [hlogX] at hKle
    have : (L / 2 + 2 * Real.log L) / Real.log 2 + 1 - L / 100 / Real.log 2 ≤ 72 / 100 * L := by
      rw [show (L / 2 + 2 * Real.log L) / Real.log 2 + 1 - L / 100 / Real.log 2 =
        (49 / 100 * L + 2 * Real.log L + Real.log 2) / Real.log 2 by field_simp; ring]
      rw [div_le_iff₀ hlog2]
      nlinarith
    linarith
  · -- the range
    intro j hj
    rw [hS, Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨hj.2, ?_⟩
    have hjK : j ≤ Nat.log 2 F := by omega
    have h1 : 2 ^ j ≤ F := le_trans (Nat.pow_le_pow_right (by norm_num) hjK)
      (Nat.pow_log_le_self 2 (by omega))
    have : ((2 ^ j : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  · -- the identity and the tail
    have hρ0 : 0 ≤ ρ.re := hρ.le
    have hsumm : Summable (bT T ρ) := by
      apply Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) / Y))
      · obtain ⟨g, hg, hb, _⟩ := tail_est hY1 (le_refl (0 : ℝ)) 0 (by simp)
        refine (hg.of_nonneg_of_le (fun i => by positivity) (fun i => ?_))
        simpa using hb i
      · exact fun n => bT_norm_le T hρ0 n
    set k : ℕ := 2 ^ K + 1 with hk
    have hsplit := hsumm.sum_add_tsum_nat_add k
    have hblock := block_sum (bT T ρ) K
    have hb0 : bT T ρ 0 = 0 := by simp [bT, aC]
    have hP1 : 1 ≤ P := by rw [hPL]; exact Real.one_le_exp (by linarith)
    have hb1 : bT T ρ 1 = (Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ) := by
      unfold bT
      rw [aC_one T hT0.le (by rw [← hPdef]; linarith)]
      simp
    have hzero : ∀ j ∈ Finset.range K, j ∉ S → ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), bT T ρ n = 0 := by
      intro j hjK hjS
      have hj : (2 : ℝ) ^ j < P := by
        rw [hS, Finset.mem_filter] at hjS
        push Not at hjS
        exact hjS hjK
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn2 : 2 ≤ n := by have := Nat.one_le_two_pow (n := j); omega
      have hnM : (n : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := by
        have : (n : ℝ) ≤ ((2 * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast hn.2
        push_cast at this
        rw [← hPdef]; linarith
      simp [bT, aC_zero_of hn2 hnM]
    have hfilt : ∑ j ∈ Finset.range K, ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), bT T ρ n =
        ∑ j ∈ S, Db T (2 ^ j) ρ := by
      rw [hS, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs with h
      · rw [Db_eq]
      · exact hzero j hj (by rw [hS, Finset.mem_filter]; exact fun h' => h h'.2)
    have hid : Iser T ρ - (Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ) - ∑ j ∈ S, Db T (2 ^ j) ρ =
        ∑' i, bT T ρ (i + k) := by
      unfold Iser
      rw [← hsplit, hblock, hb0, hb1, hfilt]
      ring
    rw [hid]
    have hXk : X ≤ (k : ℝ) := by
      rw [hk]; push_cast; push_cast at hXK; linarith
    obtain ⟨g, hg, hb, hgs⟩ := tail_est hY1 (by linarith) k hXk
    have hnorm : ‖∑' i, bT T ρ (i + k)‖ ≤ ∑' i, g i :=
      tsum_of_norm_bounded hg.hasSum (fun i => (bT_norm_le T hρ0 (i + k)).trans (hb i))
    refine hnorm.trans (hgs.trans ?_)
    -- numerics: `exp(-L²/2) (2Y+1)² ≤ 1/100`
    have hXY : -X / (2 * Y) = -(L ^ 2 / 2) := by
      rw [hXdef]; field_simp
    rw [hXY]
    have h9 : (2 * Y + 1) ^ 2 ≤ 9 * Real.exp L := by
      rw [← hTL, ← hYsq]; nlinarith
    have hexp : Real.exp (-(L ^ 2 / 2)) * Real.exp L ≤ 1 / 900 := by
      rw [← Real.exp_add]
      have h1 : -(L ^ 2 / 2) + L ≤ -L := by nlinarith
      have h2 : Real.exp (-L) ≤ 1 / 900 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        have := Real.add_one_le_exp L
        norm_num; linarith
      exact (Real.exp_le_exp.mpr h1).trans h2
    calc Real.exp (-(L ^ 2 / 2)) * (2 * Y + 1) ^ 2 ≤ Real.exp (-(L ^ 2 / 2)) * (9 * Real.exp L) := by
          gcongr
      _ = 9 * (Real.exp (-(L ^ 2 / 2)) * Real.exp L) := by ring
      _ ≤ 9 * (1 / 900) := by gcongr
      _ = 1 / 100 := by norm_num

end GuthMaynard.CitedZeros.MP23

open Complex MeasureTheory Filter Topology Set

namespace GuthMaynard.CitedZeros.MP23

/-! ## Assembly -/

theorem mp23_dev :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      let D : ℕ → ℂ → ℂ := fun N s => ∑ n ∈ Finset.Ioc N (2 * N),
        ((∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
            (ArithmeticFunction.moebius d : ℂ)) * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)) *
          (n : ℂ) ^ (-s)
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ∈ Set.Icc T (2 * T) →
        (∃ j : ℕ, (2 : ℝ) ^ j ∈ Set.Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2) ∧
            1 / (3 * Real.log T) ≤ ‖D (2 ^ j) ρ‖) ∨
        1 / 3 ≤ ‖(1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
          let s : ℂ := ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I
          (T : ℂ) ^ (s / 2) * Complex.Gamma s * M (ρ + s) * riemannZeta (ρ + s)‖ := by
  obtain ⟨K, hK0, hK⟩ := contour_shift
  obtain ⟨T₁, hT₁⟩ := res_small (1 / 100 / (K + 1)) (by positivity)
  obtain ⟨T₂, hT₂⟩ := dyadic_split
  refine ⟨max (max T₁ T₂) 100000, fun T hT => ?_⟩
  intro D M ρ hρ hγ
  have hT10' : (100000 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hT10 : (10000 : ℝ) ≤ T := by linarith
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hγ1 : 1 ≤ ρ.im := by linarith [hγ.1]
  obtain ⟨hβ0, hβ1⟩ := zero_re_pos_lt_one hρ (by linarith)
  obtain ⟨S, hScard, hSmem, hSerr⟩ := hT₂ T hT2 ρ hβ0
  by_cases hex : ∃ j : ℕ, (2 : ℝ) ^ j ∈ Set.Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2) ∧
      1 / (3 * Real.log T) ≤ ‖D (2 ^ j) ρ‖
  · exact Or.inl hex
  right
  push Not at hex
  have hlog : 9 ≤ Real.log T := by
    have h1 : Real.log 100000 ≤ Real.log T := Real.log_le_log (by norm_num) hT10'
    have h2 : (9 : ℝ) ≤ Real.log 100000 := by
      rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      have h3 : Real.log 10 = Real.log 2 + Real.log 5 := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have h5 : Real.log 4 < Real.log 5 := Real.log_lt_log (by norm_num) (by norm_num)
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      push_cast; nlinarith
    linarith
  -- the dyadic sum is small
  have hDsum : ‖∑ j ∈ S, Db T (2 ^ j) ρ‖ ≤ 24 / 100 := by
    calc ‖∑ j ∈ S, Db T (2 ^ j) ρ‖ ≤ ∑ j ∈ S, ‖Db T (2 ^ j) ρ‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ S, 1 / (3 * Real.log T) := by
          apply Finset.sum_le_sum
          intro j hj
          exact (hex j (hSmem j hj)).le
      _ = S.card * (1 / (3 * Real.log T)) := by simp
      _ ≤ 72 / 100 * Real.log T * (1 / (3 * Real.log T)) := by gcongr
      _ = 24 / 100 := by field_simp; ring
  -- `e^{-1/Y}` is close to `1`
  have hY : (100 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    have : (10000 : ℝ) ^ (1 / 2 : ℝ) = 100 := by
      rw [show (10000 : ℝ) = 100 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← this]; exact Real.rpow_le_rpow (by norm_num) hT10 (by norm_num)
  have hexp : 99 / 100 ≤ Real.exp (-1 / T ^ (1 / 2 : ℝ)) := by
    have h1 := Real.add_one_le_exp (-1 / T ^ (1 / 2 : ℝ))
    have h2 : 1 / T ^ (1 / 2 : ℝ) ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have h3 : -1 / T ^ (1 / 2 : ℝ) = -(1 / T ^ (1 / 2 : ℝ)) := by ring
    linarith
  have hI : 64 / 100 ≤ ‖Iser T ρ‖ := by
    have e1 : (Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ) = Iser T ρ -
        (Iser T ρ - (Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ) - ∑ j ∈ S, Db T (2 ^ j) ρ) -
        ∑ j ∈ S, Db T (2 ^ j) ρ := by ring
    have e2 : ‖(Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ)‖ = Real.exp (-1 / T ^ (1 / 2 : ℝ)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h3 := norm_sub_le (Iser T ρ -
        (Iser T ρ - (Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ) - ∑ j ∈ S, Db T (2 ^ j) ρ))
        (∑ j ∈ S, Db T (2 ^ j) ρ)
    have h4 := norm_sub_le (Iser T ρ)
        (Iser T ρ - (Real.exp (-1 / T ^ (1 / 2 : ℝ)) : ℂ) - ∑ j ∈ S, Db T (2 ^ j) ρ)
    rw [← e1, e2] at h3
    linarith
  have hR : ‖Res T ρ‖ ≤ 1 / 100 / (K + 1) := hT₁ T hT1 ρ hβ0 hβ1 hγ.1
  have hshift := hK T (by linarith) ρ hρ hβ0 hβ1 hγ1
  have hKR : K * ‖Res T ρ‖ ≤ 1 / 100 := by
    calc K * ‖Res T ρ‖ ≤ K * (1 / 100 / (K + 1)) := by gcongr
      _ ≤ 1 / 100 := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith
  rw [mellin_line (by linarith) hβ0] at hshift
  have hfin : 1 / 3 ≤ ‖lineInt T ρ (1 / 2 - ρ.re)‖ := by
    have := norm_sub_norm_le (Iser T ρ) (Iser T ρ - lineInt T ρ (1 / 2 - ρ.re))
    rw [sub_sub_cancel] at this
    rw [norm_sub_rev] at hshift
    linarith
  exact hfin

end GuthMaynard.CitedZeros.MP23

namespace GuthMaynard.CitedZeros

theorem mp23_dev : type_of% @GuthMaynard.CitedZeros.MP23.mp23_dev :=
  GuthMaynard.CitedZeros.MP23.mp23_dev

end GuthMaynard.CitedZeros

open scoped ENNReal in
theorem solution :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      let D : ℕ → ℂ → ℂ := fun N s => ∑ n ∈ Finset.Ioc N (2 * N),
        ((∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)),
            (ArithmeticFunction.moebius d : ℂ)) * (Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) : ℂ)) *
          (n : ℂ) ^ (-s)
      let M : ℂ → ℂ := fun s => ∑ m ∈ Finset.Icc 1 ⌊2 * T ^ (1 / 100 : ℝ)⌋₊,
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)
      ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.im ∈ Set.Icc T (2 * T) →
        (∃ j : ℕ, (2 : ℝ) ^ j ∈ Set.Icc (T ^ (1 / 100 : ℝ)) (T ^ (1 / 2 : ℝ) * Real.log T ^ 2) ∧
            1 / (3 * Real.log T) ≤ ‖D (2 ^ j) ρ‖) ∨
        1 / 3 ≤ ‖(1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ,
          let s : ℂ := ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I
          (T : ℂ) ^ (s / 2) * Complex.Gamma s * M (ρ + s) * riemannZeta (ρ + s)‖ :=
  GuthMaynard.CitedZeros.mp23_dev
