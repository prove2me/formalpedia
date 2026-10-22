-- Prove2me | solution 1 for NatureSLT.Kernels.regularized_fourier_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:57:03.323982+00:00
-- url     : https://prove2.me/submissions/00c997d0-1373-4c74-9ee9-b9f4127ca2cd

import Mathlib
open MeasureTheory

noncomputable def g70slt_G (b : ℝ) (u : ℝ) : ℂ := ((Real.cosh (b * (1 / 2 - u)) : ℝ) : ℂ)
noncomputable def g70slt_G' (b : ℝ) (u : ℝ) : ℂ := ((-b * Real.sinh (b * (1 / 2 - u)) : ℝ) : ℂ)

theorem g70slt_dG (b u : ℝ) : HasDerivAt (g70slt_G b) (g70slt_G' b u) u := by
  have h : HasDerivAt (fun u : ℝ => Real.cosh (b * (1 / 2 - u)))
      (-b * Real.sinh (b * (1 / 2 - u))) u := by
    have h1 : HasDerivAt (fun u : ℝ => b * (1 / 2 - u)) (-b) u := by
      exact (((hasDerivAt_id u).const_sub (1/2)).const_mul b).congr_deriv (by ring)
    have := (Real.hasDerivAt_cosh (b * (1 / 2 - u))).comp u h1
    exact this.congr_deriv (by ring)
  exact h.ofReal_comp

theorem g70slt_dG' (b u : ℝ) : HasDerivAt (g70slt_G' b) ((b ^ 2 : ℂ) * g70slt_G b u) u := by
  have h : HasDerivAt (fun u : ℝ => -b * Real.sinh (b * (1 / 2 - u)))
      (b ^ 2 * Real.cosh (b * (1 / 2 - u))) u := by
    have h1 : HasDerivAt (fun u : ℝ => b * (1 / 2 - u)) (-b) u := by
      exact (((hasDerivAt_id u).const_sub (1/2)).const_mul b).congr_deriv (by ring)
    have := ((Real.hasDerivAt_sinh (b * (1 / 2 - u))).comp u h1).const_mul (-b)
    exact this.congr_deriv (by ring)
  have := h.ofReal_comp
  refine this.congr_deriv ?_
  simp only [g70slt_G]; push_cast; ring

theorem g70slt_contG (b : ℝ) : Continuous (g70slt_G b) := by
  unfold g70slt_G; fun_prop
theorem g70slt_contG' (b : ℝ) : Continuous (g70slt_G' b) := by
  unfold g70slt_G'; fun_prop

theorem g70slt_coeff (b : ℝ) (hb : 0 < b) (n : ℤ) :
    fourierCoeffOn zero_lt_one (g70slt_G b) n =
      ((2 * b * Real.sinh (b / 2) / (4 * Real.pi ^ 2 * n ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, sub_zero, div_one]
    have hI : ∫ x in (0:ℝ)..1, g70slt_G b x = ((2 * Real.sinh (b / 2) / b : ℝ) : ℂ) := by
      unfold g70slt_G
      rw [intervalIntegral.integral_ofReal]
      congr 1
      have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun u : ℝ => -Real.sinh (b * (1 / 2 - u)) / b)
          (Real.cosh (b * (1 / 2 - x))) x := by
        intro x _
        have h1 : HasDerivAt (fun u : ℝ => b * (1 / 2 - u)) (-b) x := by
          exact (((hasDerivAt_id x).const_sub (1/2)).const_mul b).congr_deriv (by ring)
        have := (((Real.hasDerivAt_sinh (b * (1 / 2 - x))).comp x h1).neg).div_const b
        exact this.congr_deriv (by field_simp)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((Real.continuous_cosh.comp (by fun_prop)).intervalIntegrable _ _)]
      have : b * (1 / 2 - 1) = -(b / 2) := by ring
      have h2 : b * (1 / 2 - 0) = b / 2 := by ring
      rw [this, h2, Real.sinh_neg]; ring
    rw [hI]; congr 1
    have hb2 : (4 * Real.pi ^ 2 * ((0:ℤ):ℝ) ^ 2 + b ^ 2) = b ^ 2 := by simp
    rw [hb2]; field_simp
  · have hz : (-2 * Real.pi * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, Complex.I_ne_zero, this]
    have e1 := fourierCoeffOn_of_hasDerivAt zero_lt_one hn (fun x _ => g70slt_dG b x)
      ((g70slt_contG' b).intervalIntegrable _ _)
    have e2 := fourierCoeffOn_of_hasDerivAt zero_lt_one hn (fun x _ => g70slt_dG' b x)
      ((continuous_const.mul (g70slt_contG b)).intervalIntegrable 0 1)
    rw [fourierCoeffOn.const_mul] at e2
    simp only [QuotientAddGroup.mk_zero, fourier_eval_zero, Complex.ofReal_one, Complex.ofReal_zero, one_mul, sub_zero] at e1 e2
    have hG : g70slt_G b 1 - g70slt_G b 0 = 0 := by
      unfold g70slt_G
      have : b * (1 / 2 - 1) = -(b * (1 / 2 - 0)) := by ring
      rw [this, Real.cosh_neg, sub_self]
    have hG' : g70slt_G' b 1 - g70slt_G' b 0 = ((2 * b * Real.sinh (b / 2) : ℝ) : ℂ) := by
      unfold g70slt_G'
      have : b * (1 / 2 - 1) = -(b / 2) := by ring
      have h2 : b * (1 / 2 - 0) = b / 2 := by ring
      rw [this, h2, Real.sinh_neg]; push_cast; ring
    rw [hG] at e1; rw [hG'] at e2
    set C := fourierCoeffOn zero_lt_one (g70slt_G b) n
    set D := fourierCoeffOn zero_lt_one (g70slt_G' b) n
    set z : ℂ := -2 * Real.pi * Complex.I * n with hzdef
    have hz2 : z ^ 2 = -(4 * Real.pi ^ 2 * n ^ 2) := by
      rw [hzdef]; ring_nf; rw [Complex.I_sq]; ring
    have f1 : C * z = -D := by rw [e1]; field_simp; ring
    have f2 : D * z = ((2 * b * Real.sinh (b / 2) : ℝ) : ℂ) - b ^ 2 * C := by
      rw [e2]; field_simp
    have key : C * (4 * Real.pi ^ 2 * n ^ 2 + b ^ 2) = ((2 * b * Real.sinh (b / 2) : ℝ) : ℂ) := by
      have : C * z ^ 2 = -(D * z) := by rw [sq, ← mul_assoc, f1]; ring
      rw [hz2, f2] at this; linear_combination -this
    have hden : (4 * Real.pi ^ 2 * n ^ 2 + b ^ 2 : ℂ) ≠ 0 := by
      have : (0:ℝ) < 4 * Real.pi ^ 2 * n ^ 2 + b ^ 2 := by positivity
      exact_mod_cast this.ne'
    have hdenR : (0:ℝ) < 4 * Real.pi ^ 2 * n ^ 2 + b ^ 2 := by positivity
    rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hdenR.ne')]
    rw [← key]; push_cast; ring

theorem g70slt_fco_congr (f : ℝ → ℂ) (n : ℤ) {a b b' : ℝ} (h : a < b) (h' : a < b')
    (e : b = b') : fourierCoeffOn h f n = fourierCoeffOn h' f n := by subst e; rfl

noncomputable def g70slt_c (b : ℝ) (n : ℤ) : ℝ :=
  2 * b * Real.sinh (b / 2) / (4 * Real.pi ^ 2 * n ^ 2 + b ^ 2)

theorem g70slt_csum (b : ℝ) (hb : 0 < b) : Summable (g70slt_c b) := by
  have hs : 0 ≤ Real.sinh (b / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left
      (2 * b * Real.sinh (b / 2) / (4 * Real.pi ^ 2))) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold g70slt_c; positivity), g70slt_c]
  rw [div_mul_div_comm, mul_one]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg b]

theorem g70slt_pointwise (b : ℝ) (hb : 0 < b) (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    HasSum (fun n : ℤ => ((g70slt_c b n : ℝ) : ℂ) * fourier n (u : UnitAddCircle))
      (g70slt_G b u) := by
  have hGe : g70slt_G b 0 = g70slt_G b 1 := by
    unfold g70slt_G
    have : b * (1 / 2 - 1) = -(b * (1 / 2 - 0)) := by ring
    rw [this, Real.cosh_neg]
  let F : C(UnitAddCircle, ℂ) := ⟨AddCircle.liftIco 1 0 (g70slt_G b),
    AddCircle.liftIco_zero_continuous hGe (g70slt_contG b).continuousOn⟩
  have hcoef : ∀ n, fourierCoeff F n = ((g70slt_c b n : ℝ) : ℂ) := by
    intro n
    have := fourierCoeff_liftIco_eq (T := 1) (a := 0) (g70slt_G b) n
    rw [g70slt_c, ← g70slt_coeff b hb n]
    exact this.trans (g70slt_fco_congr _ _ _ _ (zero_add 1))
  have hsum : Summable (fourierCoeff F) := by
    exact (Complex.summable_ofReal.mpr (g70slt_csum b hb)).congr (fun n => (hcoef n).symm)
  have key : ∀ v ∈ Set.Ico (0:ℝ) 1,
      HasSum (fun n : ℤ => ((g70slt_c b n : ℝ) : ℂ) * fourier n (v : UnitAddCircle))
        (g70slt_G b v) := by
    intro v hv
    have h := has_pointwise_sum_fourier_series_of_summable hsum (v : UnitAddCircle)
    simp_rw [hcoef, smul_eq_mul] at h
    convert h using 1
    show g70slt_G b v = AddCircle.liftIco 1 0 (g70slt_G b) v
    rw [AddCircle.liftIco_coe_apply (by rwa [zero_add])]
  rcases eq_or_lt_of_le hu.2 with h1 | h1
  · subst h1
    have := key 0 ⟨le_rfl, zero_lt_one⟩
    rw [← hGe]
    convert this using 3 with n
    rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
  · exact key u ⟨hu.1, h1⟩

theorem g70slt_re (b : ℝ) (n : ℤ) (u : ℝ) :
    (((g70slt_c b n : ℝ) : ℂ) * fourier n (u : UnitAddCircle)).re =
      g70slt_c b n * Real.cos (2 * Real.pi * n * u) := by
  rw [fourier_coe_apply, Complex.re_ofReal_mul]
  congr 1
  have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (u : ℂ) / ((1 : ℝ) : ℂ)) =
      ((2 * Real.pi * n * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem g70slt_cos_series (b : ℝ) (hb : 0 < b) (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
    HasSum (fun k : ℕ => 2 * g70slt_c b ((k + 1 : ℕ) : ℤ) *
      Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u))
      (Real.cosh (b * (1 / 2 - u)) - g70slt_c b 0) := by
  have h := (g70slt_pointwise b hb u hu).nat_add_neg
  have h2 := Complex.hasSum_re h
  have hc : ∀ k : ℕ, g70slt_c b (-(k : ℤ)) = g70slt_c b k := by
    intro k; unfold g70slt_c; push_cast; ring
  have e : ∀ k : ℕ, ((((g70slt_c b k : ℝ) : ℂ) * fourier (k : ℤ) (u : UnitAddCircle)) +
      (((g70slt_c b (-(k : ℤ)) : ℝ) : ℂ) * fourier (-(k : ℤ)) (u : UnitAddCircle))).re =
      2 * g70slt_c b k * Real.cos (2 * Real.pi * (k : ℝ) * u) := by
    intro k
    rw [Complex.add_re, g70slt_re, g70slt_re, hc]
    push_cast
    rw [show 2 * Real.pi * (-(k : ℝ)) * u = -(2 * Real.pi * k * u) by ring, Real.cos_neg]
    ring
  simp only [e] at h2
  have e0 : (g70slt_G b u + ((g70slt_c b 0 : ℝ) : ℂ) * fourier (0 : ℤ) (u : UnitAddCircle)).re =
      Real.cosh (b * (1 / 2 - u)) + g70slt_c b 0 := by
    rw [Complex.add_re, g70slt_re]
    simp only [g70slt_G, Complex.ofReal_re, Int.cast_zero, mul_zero, zero_mul, Real.cos_zero,
      mul_one]
  have h2' : HasSum (fun k : ℕ => 2 * g70slt_c b k * Real.cos (2 * Real.pi * (k : ℝ) * u))
      (Real.cosh (b * (1 / 2 - u)) + g70slt_c b 0) := by
    rwa [e0] at h2
  have h3 := (hasSum_nat_add_iff' 1).mpr h2'
  have hv : Real.cosh (b * (1 / 2 - u)) - g70slt_c b 0 = Real.cosh (b * (1 / 2 - u)) +
      g70slt_c b 0 - ∑ i ∈ Finset.range 1, 2 * g70slt_c b (i : ℤ) *
        Real.cos (2 * Real.pi * (i : ℝ) * u) := by simp; ring
  rw [hv]; exact h3


/-- Eq. (6.33) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.5.1, p. 198):
for `γ > 0` and real `x_i, x_j` with `0 ≤ |x_i - x_j| ≤ 2π`, the series
`Σ_{k=1}^∞ (cos kx_i cos kx_j + sin kx_i sin kx_j)/(1 + γ²k²)` converges and
`K(x_i, x_j) = 1/2 + Σ_{k=1}^∞ (cos kx_i cos kx_j + sin kx_i sin kx_j)/(1 + γ²k²)
  = (π/(2γ)) ch((π - |x_i - x_j|)/γ) / sh(π/γ)`.
The page does not state the range of `γ`; `γ > 0` is added (at `γ = 0` the right side is
undefined). The sum over `k ≥ 1` is written over `k : ℕ` with `k + 1` in place of `k`. -/
theorem solution (γ : ℝ) (hγ : 0 < γ) (xi xj : ℝ)
    (hx : |xi - xj| ≤ 2 * Real.pi) :
    Summable (fun k : ℕ =>
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj)) / (1 + γ ^ 2 * (k + 1) ^ 2)) ∧
    1 / 2 + ∑' k : ℕ,
        (Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj)) / (1 + γ ^ 2 * (k + 1) ^ 2) =
      Real.pi / (2 * γ) * Real.cosh ((Real.pi - |xi - xj|) / γ) / Real.sinh (Real.pi / γ) := by
  set d := xi - xj with hd
  have hpi := Real.pi_pos
  set b : ℝ := 2 * Real.pi / γ with hbdef
  have hb : 0 < b := by positivity
  set u : ℝ := |d| / (2 * Real.pi) with hudef
  have hu : u ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · rw [hudef, div_le_one (by positivity)]; exact hx
  set s := Real.sinh (Real.pi / γ) with hsdef
  have hs : 0 < s := Real.sinh_pos_iff.mpr (by positivity)
  have hb2 : b / 2 = Real.pi / γ := by rw [hbdef]; ring
  have h := g70slt_cos_series b hb u hu
  set K : ℝ := 2 * γ * s / Real.pi with hK
  have hK0 : K ≠ 0 := by positivity
  have hterm : ∀ k : ℕ, 2 * g70slt_c b ((k + 1 : ℕ) : ℤ) *
      Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u) =
      K * ((Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj)) / (1 + γ ^ 2 * (k + 1) ^ 2)) := by
    intro k
    have hcos : Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u) =
        Real.cos ((k + 1) * xi) * Real.cos ((k + 1) * xj) +
          Real.sin ((k + 1) * xi) * Real.sin ((k + 1) * xj) := by
      rw [← Real.cos_sub]
      have e1 : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) * u = ((k:ℝ) + 1) * |d| := by
        rw [hudef]; push_cast; field_simp
      rw [e1]
      rcases abs_cases d with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1, hd]; ring_nf
      · rw [h1, ← Real.cos_neg, hd]; ring_nf
    rw [hcos, g70slt_c, hb2, ← hsdef]
    push_cast
    rw [hK, hbdef]
    field_simp
    ring
  simp only [hterm] at h
  have ht := h.div_const K
  simp only [mul_div_cancel_left₀ _ hK0] at ht
  refine ⟨ht.summable, ?_⟩
  rw [ht.tsum_eq]
  have hc0 : g70slt_c b 0 = γ * s / Real.pi := by
    rw [g70slt_c, hb2, ← hsdef, hbdef]; push_cast; field_simp; ring
  have hcosh : b * (1 / 2 - u) = (Real.pi - |xi - xj|) / γ := by
    rw [hbdef, hudef, ← hd]; field_simp
  rw [hc0, hcosh, hK, ← hd]
  field_simp
  ring

