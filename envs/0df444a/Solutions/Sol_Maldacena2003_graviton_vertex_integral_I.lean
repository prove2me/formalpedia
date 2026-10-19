-- Prove2me | solution 1 for Maldacena2003.graviton_vertex_integral_I
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:27:52.24138+00:00
-- url     : https://prove2.me/submissions/9a7924a5-2951-4f35-847b-915811cf1f97

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology MeasureTheory Set

namespace GVAux

/-- `(-η)^n e^{εη}` is integrable on `(-∞, 0]`. -/
lemma polyexp (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun η : ℝ => (-η) ^ n * Real.exp (ε * η)) (Iic 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ)) (b := ε)
    (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hε
  have h' : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-ε * x)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    show x ^ (n:ℝ) * Real.exp (-ε * x ^ (1:ℝ)) = x ^ n * Real.exp (-ε * x)
    rw [Real.rpow_natCast, Real.rpow_one]
  have := h'.comp_neg
  have e : -(Ici (0:ℝ)) = Iic 0 := by ext x; simp
  rw [e] at this
  refine this.congr_fun (fun x hx => ?_) measurableSet_Iic
  show (-x) ^ n * Real.exp (-ε * -x) = (-x) ^ n * Real.exp (ε * x)
  ring_nf

/-- `1/η²` is integrable on `(-∞, c]` for `c < 0`. -/
lemma inv_sq_int {c : ℝ} (hc : c < 0) : IntegrableOn (fun η : ℝ => 1 / η ^ 2) (Iic c) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (neg_pos.2 hc)
  have h' : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ici (-c)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := lt_trans (neg_pos.2 hc) hx
    show x ^ (-2:ℝ) = 1 / x ^ 2
    rw [Real.rpow_neg hx0.le, one_div]; norm_cast
  have := h'.comp_neg
  have e : -(Ici (-c)) = Iic c := by ext x; simp [neg_le]
  rw [e] at this
  simpa using this

lemma inv_sq_integral {c : ℝ} (hc : c < 0) : ∫ η in Iic c, 1 / η ^ 2 = -1 / c := by
  have := integral_Iic_of_hasDerivAt_of_tendsto' (f := fun η : ℝ => -1 / η) (m := 0)
    (f' := fun η : ℝ => 1 / η ^ 2) (a := c) (fun x hx => ?_) (inv_sq_int hc) ?_
  · simpa using this
  · have hx0 : x ≠ 0 := by have : x ≤ c := hx; linarith
    have := (hasDerivAt_inv hx0).const_mul (-1)
    have e : (fun y : ℝ => -1 / y) = fun y => -1 * y⁻¹ := by funext y; ring
    rw [e]
    exact this.congr_deriv (by field_simp)
  · have := (tendsto_inv_atBot_zero (𝕜 := ℝ)).const_mul (-1)
    simpa [div_eq_mul_inv] using this

end GVAux

namespace GVAux

noncomputable def aa (K ε : ℝ) : ℂ := (ε : ℂ) + Complex.I * K

noncomputable def Φ (K s2 p ε η : ℝ) : ℂ :=
  -Complex.exp (aa K ε * η) / η - s2 * Complex.exp (aa K ε * η) / aa K ε
    + Complex.I * p * Complex.exp (aa K ε * η) * (η / aa K ε - 1 / aa K ε ^ 2)
    + ε * Complex.exp (aa K ε * η) / (aa K ε * η)

lemma aa_ne (K ε : ℝ) (hK : 0 < K) : aa K ε ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [aa] at this
  linarith

lemma hasDeriv_Φ (K s2 p ε η : ℝ) (hK : 0 < K) (hη : η ≠ 0) :
    HasDerivAt (fun x : ℝ => Φ K s2 p ε x)
      (Complex.exp (aa K ε * η) * (1 / (η:ℂ) ^ 2 - Complex.I * K / η - s2 + Complex.I * p * η)
        - ε / aa K ε * (Complex.exp (aa K ε * η) / (η:ℂ) ^ 2)) η := by
  have ha := aa_ne K ε hK
  have hη' : (η:ℂ) ≠ 0 := by exact_mod_cast hη
  set a := aa K ε with ha_def
  have hE : HasDerivAt (fun x : ℝ => Complex.exp (a * x)) (Complex.exp (a * η) * a) η := by
    have : HasDerivAt (fun x : ℝ => a * (x:ℂ)) a η := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := η)).const_mul a
    exact this.cexp
  have hX : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 η := Complex.ofRealCLM.hasDerivAt
  have h1 := (hE.neg).div hX hη'
  have h2 := (hE.const_mul (s2:ℂ)).div_const a
  have h3 := (hE.const_mul (Complex.I * p)).mul ((hX.div_const a).sub_const (1 / a ^ 2))
  have h4 := (hE.const_mul (ε:ℂ)).div (hX.const_mul a) (mul_ne_zero ha hη')
  have h := ((h1.sub h2).add h3).add h4
  refine HasDerivAt.congr_deriv (f := fun x : ℝ => Φ K s2 p ε x) h ?_
  have hdef : a = (ε:ℂ) + Complex.I * K := rfl
  simp only [Pi.neg_apply]
  field_simp
  rw [hdef]
  ring_nf

end GVAux

namespace GVAux

lemma integrand_eq (k₁ k₂ k₃ ε η : ℝ) (hη : η ≠ 0) :
    (1 - Complex.I * (k₁ : ℂ) * (η : ℂ)) * (1 - Complex.I * (k₂ : ℂ) * (η : ℂ))
      * (1 - Complex.I * (k₃ : ℂ) * (η : ℂ))
      * Complex.exp (Complex.I * ((k₁ + k₂ + k₃ : ℝ) : ℂ) * (η : ℂ)) / (η : ℂ) ^ 2
      * (Real.exp (ε * η) : ℂ)
    = Complex.exp (aa (k₁ + k₂ + k₃) ε * η) * (1 / (η:ℂ) ^ 2 - Complex.I * ((k₁ + k₂ + k₃ : ℝ) : ℂ) / η
        - ((k₂ * k₁ + k₃ * k₁ + k₃ * k₂ : ℝ) : ℂ) + Complex.I * ((k₁ * k₂ * k₃ : ℝ) : ℂ) * η) := by
  have hη' : (η:ℂ) ≠ 0 := by exact_mod_cast hη
  have e : Complex.exp (aa (k₁ + k₂ + k₃) ε * η)
      = Complex.exp (Complex.I * ((k₁ + k₂ + k₃ : ℝ) : ℂ) * (η : ℂ)) * (Real.exp (ε * η) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; simp only [aa]; push_cast; ring
  rw [e]
  push_cast
  field_simp
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  ring_nf
  rw [Complex.I_sq, hI3]
  ring

end GVAux

namespace GVAux

lemma norm_exp_aa (K ε η : ℝ) : ‖Complex.exp (aa K ε * η)‖ = Real.exp (ε * η) := by
  rw [Complex.norm_exp]; congr 1; simp [aa]

lemma int2 (K ε c : ℝ) (hε : 0 < ε) (hc : c < 0) :
    IntegrableOn (fun η : ℝ => Complex.exp (aa K ε * η) / (η:ℂ) ^ 2) (Iic c) := by
  refine Integrable.mono' (inv_sq_int hc) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Iic
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; have : x ≤ c := hx; exact pow_ne_zero 2 (by exact_mod_cast (by linarith : x ≠ 0))
  · refine ae_restrict_of_forall_mem measurableSet_Iic (fun x hx => ?_)
    have hx' : x < 0 := lt_of_le_of_lt hx hc
    rw [norm_div, norm_exp_aa, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply div_le_div_of_nonneg_right _ (sq_nonneg x)
    exact Real.exp_le_one_iff.2 (by nlinarith)

lemma int2_bound (K ε c : ℝ) (hε : 0 < ε) (hc : c < 0) :
    ‖∫ η in Iic c, Complex.exp (aa K ε * η) / (η:ℂ) ^ 2‖ ≤ -1 / c := by
  rw [← inv_sq_integral hc]
  refine norm_integral_le_of_norm_le (inv_sq_int hc) ?_
  refine ae_restrict_of_forall_mem measurableSet_Iic (fun x hx => ?_)
  have hx' : x < 0 := lt_of_le_of_lt hx hc
  rw [norm_div, norm_exp_aa, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  apply div_le_div_of_nonneg_right _ (sq_nonneg x)
  exact Real.exp_le_one_iff.2 (by nlinarith)

end GVAux

namespace GVAux

/-- the bracket `1/η² - iK/η - s2 + ipη` -/
noncomputable def br (K s2 p η : ℝ) : ℂ :=
  1 / (η:ℂ) ^ 2 - Complex.I * (K : ℂ) / η - (s2 : ℂ) + Complex.I * (p : ℂ) * η

lemma br_norm (K s2 p η c : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s2) (hp : 0 ≤ p) (hc : c < 0) (hη : η ≤ c) :
    ‖br K s2 p η‖ ≤ (1 / c ^ 2 + K / (-c) + s2) + p * (-η) := by
  have hη0 : η < 0 := lt_of_le_of_lt hη hc
  have h1 : ‖1 / (η:ℂ) ^ 2‖ ≤ 1 / c ^ 2 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply one_div_le_one_div_of_le (by nlinarith); nlinarith
  have h2 : ‖Complex.I * (K : ℂ) / η‖ ≤ K / (-c) := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK, abs_of_neg hη0]
    apply div_le_div_of_nonneg_left hK (by linarith) (by linarith)
  have h3 : ‖(s2 : ℂ)‖ = s2 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have h4 : ‖Complex.I * (p : ℂ) * η‖ = p * (-η) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_neg hη0]
  unfold br
  calc _ ≤ ‖1 / (η:ℂ) ^ 2 - Complex.I * (K : ℂ) / η - (s2 : ℂ)‖ + ‖Complex.I * (p : ℂ) * η‖ := norm_add_le _ _
    _ ≤ (‖1 / (η:ℂ) ^ 2 - Complex.I * (K : ℂ) / η‖ + ‖(s2 : ℂ)‖) + ‖Complex.I * (p : ℂ) * η‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ ((‖1 / (η:ℂ) ^ 2‖ + ‖Complex.I * (K : ℂ) / η‖) + ‖(s2 : ℂ)‖) + ‖Complex.I * (p : ℂ) * η‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by rw [h3, h4]; linarith

lemma intf (K s2 p ε c : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s2) (hp : 0 ≤ p) (hε : 0 < ε) (hc : c < 0) :
    IntegrableOn (fun η : ℝ => Complex.exp (aa K ε * η) * br K s2 p η) (Iic c) := by
  have hb : IntegrableOn (fun η : ℝ => (1 / c ^ 2 + K / (-c) + s2) * ((-η) ^ 0 * Real.exp (ε * η))
      + p * ((-η) ^ 1 * Real.exp (ε * η))) (Iic c) := by
    have h0 := (polyexp 0 hε).mono_set (Iic_subset_Iic.2 hc.le)
    have h1 := (polyexp 1 hε).mono_set (Iic_subset_Iic.2 hc.le)
    exact (h0.const_mul _).add (h1.const_mul _)
  refine Integrable.mono' hb ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Iic
    unfold br
    have hne : ∀ x ∈ Iic c, (x:ℂ) ≠ 0 := fun x hx => by
      have : x ≤ c := hx; exact_mod_cast (by linarith : x ≠ 0)
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.add _ (by fun_prop)
    apply ContinuousOn.sub _ (by fun_prop)
    apply ContinuousOn.sub
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => pow_ne_zero 2 (hne x hx))
    · exact ContinuousOn.div (by fun_prop) (by fun_prop) hne
  · refine ae_restrict_of_forall_mem measurableSet_Iic (fun x hx => ?_)
    rw [norm_mul, norm_exp_aa]
    have := br_norm K s2 p x c hK hs hp hc hx
    simp only [pow_zero, one_mul, pow_one]
    have he := Real.exp_pos (ε * x)
    nlinarith

end GVAux

namespace GVAux

lemma Φ_eq (K s2 p ε η : ℝ) (hK : 0 < K) (hη : η ≠ 0) :
    Φ K s2 p ε η = Complex.exp (aa K ε * η) * ((-(s2:ℂ) / aa K ε - Complex.I * p / aa K ε ^ 2)
      + (Complex.I * p / aa K ε) * η + (-1 + ε / aa K ε) * (η:ℂ)⁻¹) := by
  have ha := aa_ne K ε hK
  have hη' : (η:ℂ) ≠ 0 := by exact_mod_cast hη
  unfold Φ
  field_simp
  ring

lemma exp_aa_tendsto (K ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun η : ℝ => Complex.exp (aa K ε * η)) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_exp_aa]
  exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hε)

lemma exp_aa_mul_tendsto (K ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun η : ℝ => Complex.exp (aa K ε * η) * (η:ℂ)) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    ((tendsto_neg_atBot_atTop).const_mul_atTop hε)
  have h2 := h.const_mul (1 / ε)
  rw [mul_zero] at h2
  apply h2.congr'
  filter_upwards [eventually_lt_atBot 0] with η hη
  simp only [Function.comp, norm_mul, norm_exp_aa, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hη, pow_one]
  field_simp

lemma Φ_tendsto (K s2 p ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    Tendsto (fun η : ℝ => Φ K s2 p ε η) atBot (𝓝 0) := by
  have h1 := exp_aa_tendsto K ε hε
  have h2 := exp_aa_mul_tendsto K ε hε
  have h3 : Tendsto (fun η : ℝ => (η:ℂ)⁻¹) atBot (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atBot_zero (𝕜 := ℝ))
    refine this.congr (fun η => ?_)
    simp
  have := ((h1.mul_const (-(s2:ℂ) / aa K ε - Complex.I * p / aa K ε ^ 2)).add
    (h2.mul_const (Complex.I * p / aa K ε))).add ((h1.mul h3).mul_const (-1 + ε / aa K ε))
  simp only [zero_mul, add_zero, mul_zero] at this
  apply this.congr'
  filter_upwards [eventually_lt_atBot 0] with η hη
  rw [Φ_eq K s2 p ε η hK hη.ne]
  ring

end GVAux

namespace GVAux

lemma integral_formula (k₁ k₂ k₃ ε c : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) (h₃ : 0 < k₃)
    (hε : 0 < ε) (hc : c < 0) :
    ∫ η in Iic c,
      (1 - Complex.I * (k₁ : ℂ) * (η : ℂ)) * (1 - Complex.I * (k₂ : ℂ) * (η : ℂ))
        * (1 - Complex.I * (k₃ : ℂ) * (η : ℂ))
        * Complex.exp (Complex.I * ((k₁ + k₂ + k₃ : ℝ) : ℂ) * (η : ℂ)) / (η : ℂ) ^ 2
        * (Real.exp (ε * η) : ℂ)
    = Φ (k₁ + k₂ + k₃) (k₂ * k₁ + k₃ * k₁ + k₃ * k₂) (k₁ * k₂ * k₃) ε c
      + ε / aa (k₁ + k₂ + k₃) ε * ∫ η in Iic c, Complex.exp (aa (k₁ + k₂ + k₃) ε * η) / (η:ℂ) ^ 2 := by
  set K := k₁ + k₂ + k₃ with hK
  set s2 := k₂ * k₁ + k₃ * k₁ + k₃ * k₂ with hs2
  set p := k₁ * k₂ * k₃ with hp
  have hK0 : 0 < K := by positivity
  set g : ℝ → ℂ := fun η => Complex.exp (aa K ε * η) / (η:ℂ) ^ 2 with hg
  set φ : ℝ → ℂ := fun η => Complex.exp (aa K ε * η) * br K s2 p η - ε / aa K ε * g η with hφ
  have hgi := int2 K ε c hε hc
  have hfi := intf K s2 p ε c hK0.le (by positivity) (by positivity) hε hc
  have hφi : IntegrableOn φ (Iic c) := hfi.sub (hgi.const_mul _)
  have e1 : ∫ η in Iic c,
      (1 - Complex.I * (k₁ : ℂ) * (η : ℂ)) * (1 - Complex.I * (k₂ : ℂ) * (η : ℂ))
        * (1 - Complex.I * (k₃ : ℂ) * (η : ℂ))
        * Complex.exp (Complex.I * ((k₁ + k₂ + k₃ : ℝ) : ℂ) * (η : ℂ)) / (η : ℂ) ^ 2
        * (Real.exp (ε * η) : ℂ) = ∫ η in Iic c, (φ η + ε / aa K ε * g η) := by
    refine setIntegral_congr_fun measurableSet_Iic (fun η hη => ?_)
    have hη0 : η ≠ 0 := by have : η ≤ c := hη; linarith
    rw [integrand_eq k₁ k₂ k₃ ε η hη0]
    simp only [hφ, br, hK, hs2, hp]
    ring
  rw [e1, integral_add hφi (hgi.const_mul _), integral_const_mul]
  congr 1
  have := integral_Iic_of_hasDerivAt_of_tendsto' (f := fun x : ℝ => Φ K s2 p ε x) (m := 0)
    (f' := φ) (a := c) (fun x hx => ?_) hφi (Φ_tendsto K s2 p ε hK0 hε)
  · rw [this, sub_zero]
  · have hx0 : x ≠ 0 := by have : x ≤ c := hx; linarith
    exact hasDeriv_Φ K s2 p ε x hK0 hx0

end GVAux

namespace GVAux

@[fun_prop] lemma continuous_aa (K : ℝ) : Continuous (fun ε : ℝ => aa K ε) := by
  unfold aa; fun_prop

noncomputable def R0 (K s2 p c : ℝ) : ℂ :=
  - s2 * Complex.exp (aa K 0 * c) / aa K 0
    + Complex.I * p * Complex.exp (aa K 0 * c) * (c / aa K 0 - 1 / aa K 0 ^ 2)

lemma Φ_zero (K s2 p c : ℝ) : Φ K s2 p 0 c = -Complex.exp (aa K 0 * c) / c + R0 K s2 p c := by
  unfold Φ R0; push_cast; ring

lemma first_re (K c : ℝ) : (-(Complex.I * (-Complex.exp (aa K 0 * c) / c))).re = -Real.sin (K * c) / c := by
  have e : aa K 0 * c = ((K * c : ℝ) : ℂ) * Complex.I := by simp [aa]; ring
  rw [e]
  have : -(Complex.I * (-Complex.exp (((K * c : ℝ) : ℂ) * Complex.I) / c))
      = Complex.I * Complex.exp (((K * c : ℝ) : ℂ) * Complex.I) / c := by ring
  rw [this, Complex.div_ofReal_re, Complex.I_mul_re, Complex.exp_ofReal_mul_I_im]

lemma R0_zero (K s2 p : ℝ) (hK : 0 < K) :
    (-(Complex.I * R0 K s2 p 0)).re = s2 / K + p / K ^ 2 := by
  have hK' : (K:ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have : -(Complex.I * R0 K s2 p 0) = ((s2 / K + p / K ^ 2 : ℝ) : ℂ) := by
    unfold R0 aa
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_add]
    push_cast
    field_simp
    ring_nf
  rw [this, Complex.ofReal_re]

end GVAux

theorem solution (k₁ k₂ k₃ : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) (h₃ : 0 < k₃) :
    ∃ J : ℝ → ℝ,
      (∀ η₀ : ℝ, η₀ < 0 →
        Tendsto
          (fun ε : ℝ => (-(Complex.I * ∫ η in Set.Iic η₀,
            (1 - Complex.I * (k₁ : ℂ) * (η : ℂ)) * (1 - Complex.I * (k₂ : ℂ) * (η : ℂ))
              * (1 - Complex.I * (k₃ : ℂ) * (η : ℂ))
              * Complex.exp (Complex.I * ((k₁ + k₂ + k₃ : ℝ) : ℂ) * (η : ℂ)) / (η : ℂ) ^ 2
              * (Real.exp (ε * η) : ℂ))).re)
          (𝓝[>] 0) (𝓝 (J η₀))) ∧
      Tendsto J (𝓝[<] 0)
        (𝓝 (-(k₁ + k₂ + k₃) + (k₂ * k₁ + k₃ * k₁ + k₃ * k₂) / (k₁ + k₂ + k₃)
          + k₁ * k₂ * k₃ / (k₁ + k₂ + k₃) ^ 2)) := by
  set K := k₁ + k₂ + k₃ with hK
  set s2 := k₂ * k₁ + k₃ * k₁ + k₃ * k₂ with hs2
  set p := k₁ * k₂ * k₃ with hp
  have hK0 : 0 < K := by positivity
  refine ⟨fun c => (-(Complex.I * GVAux.Φ K s2 p 0 c)).re, ?_, ?_⟩
  · intro c hc
    have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne
    have ha0 := GVAux.aa_ne K 0 hK0
    have hA : ContinuousAt (fun ε : ℝ => GVAux.Φ K s2 p ε c) 0 := by
      unfold GVAux.Φ
      fun_prop (disch := first | exact ha0 | exact hc' | exact pow_ne_zero 2 ha0 | exact mul_ne_zero ha0 hc')
    have hB : Tendsto (fun ε : ℝ => (ε:ℂ) / GVAux.aa K ε
        * ∫ η in Iic c, Complex.exp (GVAux.aa K ε * η) / (η:ℂ) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hlim : Tendsto (fun ε : ℝ => ε / K * (-1 / c)) (𝓝[>] 0) (𝓝 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        have : Continuous (fun ε : ℝ => ε / K * (-1 / c)) := by fun_prop
        simpa using this.tendsto 0
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      have h1 : K ≤ ‖GVAux.aa K ε‖ := by
        have := Complex.abs_im_le_norm (GVAux.aa K ε)
        simp [GVAux.aa, abs_of_pos hK0] at this
        exact this
      have h2 := GVAux.int2_bound K ε c hε hc
      have h3 : ε / ‖GVAux.aa K ε‖ ≤ ε / K := div_le_div_of_nonneg_left hε.le hK0 h1
      have h4 : 0 ≤ -1 / c := by apply div_nonneg_of_nonpos (by norm_num) hc.le
      exact mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
    have hsum := ((hA.tendsto.mono_left nhdsWithin_le_nhds).add hB)
    rw [add_zero] at hsum
    have hcont : Continuous (fun z : ℂ => (-(Complex.I * z)).re) := by fun_prop
    have hre := (hcont.tendsto _).comp hsum
    apply hre.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    simp only [Function.comp]
    rw [GVAux.integral_formula k₁ k₂ k₃ ε c h₁ h₂ h₃ hε hc]
  · -- J c = -sin(Kc)/c + R(c)
    have hR : ContinuousAt (fun c : ℝ => (-(Complex.I * GVAux.R0 K s2 p c)).re) 0 := by
      have ha0 := GVAux.aa_ne K 0 hK0
      unfold GVAux.R0
      fun_prop (disch := first | exact ha0 | exact pow_ne_zero 2 ha0)
    have hsin : Tendsto (fun c : ℝ => Real.sin (K * c) / c) (𝓝[<] 0) (𝓝 K) := by
      have hd : HasDerivAt (fun x : ℝ => Real.sin (K * x)) (Real.cos (K * 0) * K) 0 := by
        have : HasDerivAt (fun x : ℝ => K * x) K 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_mul K
        exact this.sin
      rw [hasDerivAt_iff_tendsto_slope_zero] at hd
      simp only [zero_add, mul_zero, Real.sin_zero, sub_zero, Real.cos_zero, one_mul, smul_eq_mul] at hd
      refine (hd.mono_left (nhdsLT_le_nhdsNE 0)).congr (fun c => ?_)
      ring
    have hlim := (hsin.neg).add (hR.tendsto.mono_left nhdsWithin_le_nhds)
    rw [GVAux.R0_zero K s2 p hK0] at hlim
    have e : -K + (s2 / K + p / K ^ 2) = -(k₁ + k₂ + k₃) + (k₂ * k₁ + k₃ * k₁ + k₃ * k₂) / (k₁ + k₂ + k₃)
          + k₁ * k₂ * k₃ / (k₁ + k₂ + k₃) ^ 2 := by rw [hK, hs2, hp]; ring
    rw [e] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with c (hc : c < 0)
    rw [GVAux.Φ_zero, mul_add, neg_add, Complex.add_re, GVAux.first_re]
    ring
