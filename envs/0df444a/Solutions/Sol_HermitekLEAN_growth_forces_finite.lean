-- Prove2me | solution 1 for HermitekLEAN.growth_forces_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:17.242544+00:00
-- url     : https://prove2.me/submissions/3ef9f2e2-bfa5-475c-a150-c26858ace6d8

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
public import Theorems.Thm_HermitekLEAN_circleSeries_fourierCoeff_hermiteCoeff
public import Theorems.Thm_HermitekLEAN_circle_representation_hermiteCoeff
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_circle
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_qkn_top_term_asymptotic
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
namespace HermitekLEAN
private theorem qkn_eventual_upper_bound (k n : ℕ) :
    ∃ R C : ℝ,
      1 ≤ R ∧ 0 < C ∧ ∀ r ≥ R, ‖(qkn k n r : ℂ)‖ ≤ C * r ^ n := by
  obtain ⟨c0, _, hc0⟩ := qkn_top_term_asymptotic k n
  obtain ⟨R0, hR0⟩ := hc0 1 zero_lt_one
  let C : ℝ := ‖(c0 : ℂ)‖ + 1
  refine ⟨max 1 R0, C, le_max_left 1 R0, by positivity, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left 1 R0) hr
  have hrR0 : R0 ≤ r := le_trans (le_max_right 1 R0) hr
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr1
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrpow_nonneg : 0 ≤ r ^ n := pow_nonneg hr_nonneg _
  have hrpow_pos : 0 < r ^ n := pow_pos hr_pos _
  have hdiv_norm :
      ‖((qkn k n r : ℂ) / (r ^ n : ℂ))‖ = ‖(qkn k n r : ℂ)‖ / r ^ n := by
    rw [norm_div]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
  have happrox := hR0 r hrR0
  have hle_div : ‖(qkn k n r : ℂ)‖ / r ^ n ≤ C := by
    rw [← hdiv_norm]
    calc
      ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖
          ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ) - c0‖ + ‖c0‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              norm_add_le (((qkn k n r : ℂ) / (r ^ n : ℂ)) - c0) c0
      _ ≤ 1 + ‖c0‖ := by gcongr
      _ = C := by simp [C, add_comm]
  have hmul := mul_le_mul_of_nonneg_right hle_div hrpow_nonneg
  rwa [div_mul_cancel₀ _ hrpow_pos.ne'] at hmul
private theorem qkn_eventual_lower_bound' (k n : ℕ) :
    ∃ R c : ℝ, 0 < c ∧ ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖ := by
  obtain ⟨c, hc_ne, hc⟩ := qkn_top_term_asymptotic k n
  have hc_norm : 0 < ‖(c : ℂ)‖ := by simp [hc_ne]
  obtain ⟨R0, hR0⟩ := hc (‖(c : ℂ)‖ / 2) (by positivity)
  refine ⟨max 1 R0, ‖(c : ℂ)‖ / 2, by positivity, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left 1 R0) hr
  have hrR0 : R0 ≤ r := le_trans (le_max_right 1 R0) hr
  have hclose := hR0 r hrR0
  rw [norm_sub_rev] at hclose
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr1
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hmain : ‖(c : ℂ)‖ / 2 ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ := by
    linarith only [hclose, norm_le_norm_sub_add ((c : ℂ)) ((qkn k n r : ℂ) / (r ^ n : ℂ))]
  have hpow_nonzero : (r ^ n : ℂ) ≠ 0 :=
    pow_ne_zero n (by exact_mod_cast (ne_of_gt hr_pos))
  have hpow_norm : ‖(r ^ n : ℂ)‖ = r ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
  have hratio_mul :
      ((qkn k n r : ℂ) / (r ^ n : ℂ)) * (r ^ n : ℂ) = (qkn k n r : ℂ) := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hpow_nonzero, mul_one]
  have hnorm_mul : ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ * r ^ n = ‖(qkn k n r : ℂ)‖ := by
    rw [← hpow_norm, ← norm_mul, hratio_mul]
  calc
    (‖(c : ℂ)‖ / 2) * r ^ n ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ * r ^ n := by gcongr
    _ = ‖(qkn k n r : ℂ)‖ := hnorm_mul
private theorem coeff_eq_zero_of_qkn_eventual_bounds
    {k d n : ℕ} {g : ℕ → ℂ}
    (hdn : d < n)
    (hupper : ∃ R0 C : ℝ, 1 ≤ R0 ∧ ∀ r ≥ R0, ‖g n * (qkn k n r : ℂ)‖ ≤ C * r ^ d)
    (hlower : ∃ R c : ℝ, 0 < c ∧ ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖) :
    g n = 0 := by
  by_contra hg
  obtain ⟨R0, C, hR0, hC⟩ := hupper
  obtain ⟨R, c, hc, hR⟩ := hlower
  let C' : ℝ := max C 0
  have hC' : ∀ r ≥ R0, ‖g n * (qkn k n r : ℂ)‖ ≤ C' * r ^ d := by
    intro r hr
    have hmul : C * r ^ d ≤ C' * r ^ d := by
      have hr_nonneg : 0 ≤ r := le_trans zero_le_one (le_trans hR0 hr)
      have hpow_nonneg : 0 ≤ r ^ d := pow_nonneg hr_nonneg d
      nlinarith only [le_max_left C 0, hpow_nonneg]
    exact le_trans (hC r hr) hmul
  have hgn : 0 < ‖g n‖ := norm_pos_iff.mpr hg
  let A : ℝ := c * ‖g n‖
  have hA : 0 < A := by positivity
  have hgrow : Filter.Tendsto (fun x : ℝ => A * x ^ (n - d)) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_pow_atTop_iff).2 ⟨by omega, hA⟩
  obtain ⟨R', hR' : ∀ x ≥ R', C' + 1 ≤ A * x ^ (n - d)⟩ :=
    (Filter.tendsto_atTop_atTop.1 hgrow) (C' + 1)
  let r : ℝ := max R0 (max R R')
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact le_trans hR0 (le_max_left R0 (max R R'))
  have hrR0 : R0 ≤ r := by
    dsimp [r]
    exact le_max_left R0 (max R R')
  have hrR : R ≤ r := by
    dsimp [r]
    exact le_trans (le_max_left R R') (le_max_right R0 (max R R'))
  have hrR' : R' ≤ r := by
    dsimp [r]
    exact le_trans (le_max_right R R') (le_max_right R0 (max R R'))
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hq_lower : c * r ^ n ≤ ‖(qkn k n r : ℂ)‖ := hR r hrR
  have hmul_lower : A * r ^ n ≤ ‖g n * (qkn k n r : ℂ)‖ := by
    calc
      A * r ^ n = ‖g n‖ * (c * r ^ n) := by
        dsimp [A]
        ring
      _ ≤ ‖g n‖ * ‖(qkn k n r : ℂ)‖ := by gcongr
      _ = ‖g n * (qkn k n r : ℂ)‖ := by rw [norm_mul]
  have hineq : A * r ^ n ≤ C' * r ^ d := le_trans hmul_lower (hC' r hrR0)
  have hrd_pos : 0 < r ^ d := pow_pos hr_pos _
  have hpow_le : A * r ^ (n - d) ≤ C' := by
    have hineq'' : A * r ^ (d + (n - d)) ≤ C' * r ^ d := by
      simpa [Nat.add_sub_of_le (Nat.le_of_lt hdn)] using hineq
    have hineq' : (A * r ^ (n - d)) * r ^ d ≤ C' * r ^ d := by
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hineq''
    exact le_of_mul_le_mul_right hineq' hrd_pos
  have hpow_large : C' + 1 ≤ A * r ^ (n - d) := hR' r hrR'
  linarith only [hpow_le, hpow_large]
private lemma circleLeadingFactor_ne_zero (k : ℕ) {r : ℝ} (hr : 0 < r) :
    circleLeadingFactor k r ≠ 0 := by
  have hpos : 0 < ((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) := by positivity
  simpa [circleLeadingFactor] using hpos.ne'
private lemma norm_circleLeadingFactor_mul_cancel
    {k : ℕ} {r : ℝ} (hr : 0 < r) {f x y : ℂ} (hf : ‖f‖ = 1)
    (h : ‖circleLeadingFactor k r * f * x‖ = ‖circleLeadingFactor k r * f * y‖) :
    ‖x‖ = ‖y‖ := by
  simp only [norm_mul, hf, mul_one] at h
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (circleLeadingFactor_ne_zero k hr)) h
private theorem circle_series_norm_eq_of_modulus_eq
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k)
    (hmod : ∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖)
    (r : ℝ) (hr : 0 < r) (t : Circle) :
    ‖circleSeries k (hermiteCoeff k G) r t‖ = ‖finiteCirclePoly k r a t‖ := by
  have hGrep := circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
  have hUrep := finiteHermiteSum_circle (k := k) (a := a) (r := r) hr t
  have hnorm := hmod (circlePoint r t)
  rw [hGrep, hUrep] at hnorm
  exact norm_circleLeadingFactor_mul_cancel hr
    (by simp [fourier_apply, Circle.norm_coe]) hnorm
private theorem finiteCirclePoly_sum
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {r : ℝ} (_hr : 0 < r) (t : Circle) :
    finiteCirclePoly k r a t =
      ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t := by
  rw [finiteCirclePoly,
    show positiveTrigonometricPolynomial (frequencyBand 0 (d + 1)) (finiteCircleCoeff k r a) t =
      ∑ n ∈ frequencyBand 0 (d + 1), finiteCircleCoeff k r a n * fourier (n : ℤ) t by rfl]
  have hband : frequencyBand 0 (d + 1) = Finset.range (d + 1) := by
    simpa [HermiteLEAN.frequencyBand] using
      (show Finset.Icc 0 d = Finset.range (d + 1) by
        ext n
        simp [Finset.mem_Icc])
  rw [hband, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxle : (x : ℕ) ≤ d := Nat.le_of_lt_succ x.is_lt
  simp [finiteCircleCoeff, fourier_apply, hxle]
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖) →
            ∀ n : ℕ, d < n → hermiteCoeff k G n = 0 := by
  intro k d a hTop G hG hmod n hn
  have hupper :
      ∃ R C : ℝ,
        1 ≤ R ∧
          ∀ r ≥ R, ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ≤ C * r ^ d := by
    classical
    have hq :
        ∀ i : Fin (d + 1),
          ∃ R C : ℝ,
            1 ≤ R ∧ 0 < C ∧ ∀ r ≥ R, ‖(qkn k i.1 r : ℂ)‖ ≤ C * r ^ i.1 := by
      intro i
      simpa using qkn_eventual_upper_bound k i.1
    choose R_i C_i hR_i hC_i hqi using hq
    have hnonemptyR : (Finset.univ.image R_i).Nonempty := by
      simp_all
    have hnonemptyC : (Finset.univ.image C_i).Nonempty := by
      simp_all
    let Rbar : ℝ := (Finset.univ.image R_i).max' hnonemptyR
    let Cmax : ℝ := (Finset.univ.image C_i).max' hnonemptyC
    have hRbar_ge : ∀ i : Fin (d + 1), R_i i ≤ Rbar := by
      intro i
      dsimp [Rbar]
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hCmax_ge : ∀ i : Fin (d + 1), C_i i ≤ Cmax := by
      intro i
      dsimp [Cmax]
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hCmax_pos : 0 < Cmax := by
      dsimp [Cmax]
      exact lt_of_lt_of_le (hC_i ⟨d, Nat.lt_succ_self d⟩) (hCmax_ge ⟨d, Nat.lt_succ_self d⟩)
    refine ⟨max 1 Rbar, (∑ i : Fin (d + 1), ‖a i‖) * Cmax, le_max_left _ _, ?_⟩
    intro r hr
    have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
    have hrbar : Rbar ≤ r := le_trans (le_max_right _ _) hr
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have hqmax : ∀ i : Fin (d + 1), ‖(qkn k i.1 r : ℂ)‖ ≤ Cmax * r ^ d := by
      intro i
      have hRi : R_i i ≤ r := le_trans (hRbar_ge i) hrbar
      have hq0 : ‖(qkn k i.1 r : ℂ)‖ ≤ C_i i * r ^ i.1 := hqi i r hRi
      have hCi : C_i i ≤ Cmax := hCmax_ge i
      have hi_le : i.1 ≤ d := Nat.le_of_lt_succ i.is_lt
      have hCmax_nonneg : 0 ≤ Cmax := hCmax_pos.le
      calc
        ‖(qkn k i.1 r : ℂ)‖ ≤ C_i i * r ^ i.1 := hq0
        _ ≤ Cmax * r ^ d := by gcongr
    have hconst :
        (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d =
          (∑ i : Fin (d + 1), ‖a i‖) * Cmax * r ^ d := by rw [← Finset.sum_mul]
    have hpoly_bound :
        ∀ t : Circle, ‖finiteCirclePoly k r a t‖ ≤ (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
      intro t
      have hraw :
          ‖∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
        calc
        ‖∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t‖
            ≤ ∑ i : Fin (d + 1), ‖a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t‖ :=
              norm_sum_le _ _
        _ = ∑ i : Fin (d + 1), ‖a i‖ * ‖(qkn k i.1 r : ℂ)‖ * ‖(fourier (i.1 : ℤ)) t‖ := by
              simp_all
        _ ≤ ∑ i : Fin (d + 1), ‖a i‖ * Cmax * r ^ d := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hfour : ‖(fourier (i.1 : ℤ)) t‖ = 1 := by
                simp [fourier_apply, Circle.norm_coe]
              rw [hfour, mul_one]
              have hmul := mul_le_mul_of_nonneg_left (hqmax i) (norm_nonneg (a i))
              simpa [mul_assoc] using hmul
        _ = (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by rw [Finset.sum_mul]
      rw [finiteCirclePoly_sum a hr_pos t]
      exact hraw
    have hpoint :
        ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ≤
          (∑ i : Fin (d + 1), ‖a i‖) * Cmax * r ^ d := by
      have hbound : ∀ᵐ t ∂AddCircle.haarAddCircle,
          ‖fourier (-(n : ℤ)) t • circleSeries k (hermiteCoeff k G) r t‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
        refine Filter.Eventually.of_forall ?_
        intro t
        rw [norm_smul]
        have hfour : ‖(fourier (-(n : ℤ))) t‖ = 1 := by
          simp [fourier_apply, Circle.norm_coe]
        rw [hfour, one_mul]
        rw [circle_series_norm_eq_of_modulus_eq (k := k) (d := d) (a := a) (G := G) hG hmod r
          hr_pos t]
        exact hpoly_bound t
      have hInt0 :
          ‖∫ t : Circle, fourier (-(n : ℤ)) t • circleSeries k (hermiteCoeff k G) r t
              ∂AddCircle.haarAddCircle‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
        simpa using
          MeasureTheory.norm_integral_le_of_norm_le_const
            (μ := AddCircle.haarAddCircle) (f := fun t : Circle =>
              fourier (-(n : ℤ)) t • circleSeries k (hermiteCoeff k G) r t)
            (C := (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d) hbound
      have hfour :
          fourierCoeff (circleSeries k (hermiteCoeff k G) r) (n : ℤ) =
            hermiteCoeff k G n * (qkn k n r : ℂ) := by
        simpa using
          (circleSeries_fourierCoeff_hermiteCoeff (k := k) (G := G) hG (r := r) hr_pos n)
      rw [← hfour]
      simpa [fourierCoeff, hconst] using hInt0
    exact hpoint
  have hlower := qkn_eventual_lower_bound' k n
  exact coeff_eq_zero_of_qkn_eventual_bounds hn hupper hlower
end HermitekLEAN
