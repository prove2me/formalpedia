-- Prove2me | solution 1 for LeblSCV.Hartogs.compactly_supported_dbar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T11:08:06.022165+00:00
-- url     : https://prove2.me/submissions/3b987a05-84d8-49ff-adf6-3d26d97a36fe

import Mathlib
import Definitions.Def_LeblSCV_Shared_wirtingerBar

set_option autoImplicit false

open MeasureTheory Set Filter Topology Real
open scoped ContDiff
open Complex (I)

namespace DbarKey

/-- one-variable `∂/∂z̄` via the real Fréchet derivative -/
noncomputable def dbar1 (φ : ℂ → ℂ) (x : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ φ x 1 + I * fderiv ℝ φ x I)

/-- the unit vector `e^{iθ}` -/
noncomputable def u (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

theorem continuous_u : Continuous u := by unfold u; fun_prop

theorem polar_eq (p : ℝ × ℝ) : Complex.polarCoord.symm p = (p.1 : ℂ) * u p.2 := by
  simp [Complex.polarCoord_symm_apply, u]

theorem norm_mul_u (r θ : ℝ) : ‖(r : ℂ) * u θ‖ = |r| := by
  rw [← polar_eq (r, θ)]
  exact Complex.norm_polarCoord_symm (r, θ)

theorem hasDerivAt_u (θ : ℝ) : HasDerivAt u (I * u θ) θ := by
  have h1 := (Real.hasDerivAt_cos θ).ofReal_comp
  have h2 := ((Real.hasDerivAt_sin θ).ofReal_comp).mul_const I
  have := h1.add h2
  have h3 : I * u θ = ((-Real.sin θ : ℝ) : ℂ) + ((Real.cos θ : ℝ) : ℂ) * I := by
    rw [show u θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I from rfl]
    simp only [Complex.ofReal_neg]
    linear_combination ((Real.sin θ : ℂ)) * Complex.I_sq
  rw [h3]
  exact this

theorem lin (L : ℂ →L[ℝ] ℂ) (x : ℂ) : L x = (x.re : ℂ) * L 1 + (x.im : ℂ) * L I := by
  have hx : x = x.re • (1 : ℂ) + x.im • I := by
    simp [Complex.real_smul, Complex.re_add_im]
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem pointwise (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) (hr : r ≠ 0) :
    r • ((1 / 2 : ℂ) * (L 1 + I * L I) / ((r : ℂ) * u θ)) =
      (1 / 2 : ℂ) * (L (u θ) + I * L (I * u θ)) := by
  have hu0 : u θ ≠ 0 := by
    intro h
    have := norm_mul_u 1 θ
    rw [h] at this
    simp at this
  have hne : (r : ℂ) * u θ ≠ 0 := mul_ne_zero (by exact_mod_cast hr) hu0
  have hre1 : (u θ).re = Real.cos θ := by simp [u, -Complex.ofReal_cos, -Complex.ofReal_sin]
  have him1 : (u θ).im = Real.sin θ := by simp [u, -Complex.ofReal_cos, -Complex.ofReal_sin]
  have hre2 : (I * u θ).re = -Real.sin θ := by simp [u, -Complex.ofReal_cos, -Complex.ofReal_sin]
  have him2 : (I * u θ).im = Real.cos θ := by simp [u, -Complex.ofReal_cos, -Complex.ofReal_sin]
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [Complex.real_smul, mul_div_assoc', div_eq_iff hne, lin L (u θ), lin L (I * u θ),
    hre1, him1, hre2, him2]
  simp only [u, Complex.ofReal_neg]
  linear_combination (-(1 / 2 : ℂ) * r * (L 1 + I * L I)) * hcs +
    ((1 / 2 : ℂ) * r * ((Real.sin θ : ℂ) ^ 2 * L 1 - (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * L I)) *
      Complex.I_sq

/-- Key identity: `∫ (∂φ/∂z̄)(w) / w dA(w) = -π φ(0)` for compactly supported `C^1` `φ`. -/
theorem key (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) :
    ∫ w : ℂ, dbar1 φ w / w = -(π : ℂ) * φ 0 := by
  set D := fderiv ℝ φ with hD
  have hDc : Continuous D := hφ.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  obtain ⟨R, hR⟩ : ∃ R, tsupport φ ⊆ Metric.closedBall 0 R :=
    hs.isCompact.isBounded.subset_closedBall 0
  set R' : ℝ := max R 0 + 1 with hR'
  have hR'pos : 0 < R' := by positivity
  have hRR' : R < R' := by have := le_max_left R 0; linarith
  have hnot : ∀ x : ℂ, R < ‖x‖ → x ∉ tsupport φ := by
    intro x hx h
    have := hR h
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hφout : ∀ x : ℂ, R < ‖x‖ → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hnot x hx)
  have hDout : ∀ x : ℂ, R < ‖x‖ → D x = 0 := by
    intro x hx
    by_contra h
    exact hnot x hx (support_fderiv_subset ℝ h)
  set Ar : ℝ × ℝ → ℂ := fun p => D ((p.1 : ℂ) * u p.2) (u p.2) with hAr
  set Aθ : ℝ × ℝ → ℂ := fun p => D ((p.1 : ℂ) * u p.2) (I * u p.2) with hAθ
  have hpt : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * u p.2 :=
    (Complex.continuous_ofReal.comp continuous_fst).mul (continuous_u.comp continuous_snd)
  have hArc : Continuous Ar := (hDc.comp hpt).clm_apply (continuous_u.comp continuous_snd)
  have hAθc : Continuous Aθ :=
    (hDc.comp hpt).clm_apply (continuous_const.mul (continuous_u.comp continuous_snd))
  set S : Set (ℝ × ℝ) := Ioo 0 R' ×ˢ Ioo (-π) π with hS
  have hSsub : S ⊆ Icc 0 R' ×ˢ Icc (-π) π := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hcpt : IsCompact (Icc 0 R' ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  have hInt : ∀ f : ℝ × ℝ → ℂ, Continuous f → IntegrableOn f S := fun f hf =>
    (hf.continuousOn.integrableOn_compact hcpt).mono_set hSsub
  -- polar coordinates
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hcongr : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 • (dbar1 φ (Complex.polarCoord.symm p) / Complex.polarCoord.symm p) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, (1 / 2 : ℂ) * (Ar p + I * Aθ p) := by
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    intro p hp
    dsimp only
    rw [polar_eq]
    exact pointwise (D ((p.1 : ℂ) * u p.2)) p.1 p.2 (ne_of_gt hp.1)
  rw [hcongr]
  have hrestr : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, (1 / 2 : ℂ) * (Ar p + I * Aθ p) =
      ∫ p in S, (1 / 2 : ℂ) * (Ar p + I * Aθ p) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioi.prod measurableSet_Ioo) (prod_mono Ioo_subset_Ioi_self subset_rfl) ?_
    intro p hp
    have h1 : 0 < p.1 := hp.1.1
    have h2 : R' ≤ p.1 := by
      by_contra h
      exact hp.2 ⟨⟨h1, lt_of_not_ge h⟩, hp.1.2⟩
    have hz : D ((p.1 : ℂ) * u p.2) = 0 := by
      apply hDout
      rw [norm_mul_u, abs_of_pos h1]
      linarith
    simp [hAr, hAθ, hz]
  rw [hrestr, integral_const_mul, integral_add (hInt _ hArc) ((hInt _ hAθc).const_mul I),
    integral_const_mul]
  -- the angular part vanishes
  have hθ : ∫ p in S, Aθ p = 0 := by
    have hI := hInt _ hAθc
    rw [Measure.volume_eq_prod] at hI ⊢
    rw [setIntegral_prod _ hI]
    have hz : ∀ r ∈ Ioo (0 : ℝ) R', ∫ θ in Ioo (-π) π, Aθ (r, θ) = 0 := by
      intro r hr
      have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr.1)
      have hder : ∀ θ : ℝ, HasDerivAt (fun θ => φ ((r : ℂ) * u θ)) ((r : ℂ) * Aθ (r, θ)) θ := by
        intro θ
        have hγ : HasDerivAt (fun θ => (r : ℂ) * u θ) ((r : ℂ) * (I * u θ)) θ :=
          (hasDerivAt_u θ).const_mul (r : ℂ)
        have := (hdiff ((r : ℂ) * u θ)).hasFDerivAt.comp_hasDerivAt θ hγ
        have hk : (r : ℂ) * Aθ (r, θ) = D ((r : ℂ) * u θ) ((r : ℂ) * (I * u θ)) := by
          show (r : ℂ) * D ((r : ℂ) * u θ) (I * u θ) = _
          rw [show (r : ℂ) * (I * u θ) = r • (I * u θ) from (Complex.real_smul).symm, map_smul,
            Complex.real_smul]
        rw [hk]
        exact this
      have hc : Continuous fun θ : ℝ => (r : ℂ) * Aθ (r, θ) :=
        continuous_const.mul (hAθc.comp (Continuous.prodMk continuous_const continuous_id))
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hder θ)
        (hc.intervalIntegrable (-π) π)
      have hends : φ ((r : ℂ) * u π) = φ ((r : ℂ) * u (-π)) := by simp [u]
      rw [hends, sub_self, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Ioc_eq_integral_Ioo] at hftc
      exact (mul_eq_zero.1 hftc).resolve_left hr0
    rw [setIntegral_congr_fun measurableSet_Ioo hz]
    exact integral_zero _ _
  -- the radial part
  have hr : ∫ p in S, Ar p = (2 * π : ℝ) * (-φ 0) := by
    have hI : IntegrableOn (fun z : ℝ × ℝ => Ar z.swap) (Ioo (-π) π ×ˢ Ioo 0 R') := by
      have hc : Continuous fun z : ℝ × ℝ => Ar z.swap := hArc.comp continuous_swap
      have hsub : Ioo (-π) π ×ˢ Ioo 0 R' ⊆ Icc (-π) π ×ˢ Icc 0 R' :=
        prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
      exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set hsub
    rw [Measure.volume_eq_prod] at hI ⊢
    rw [hS, ← setIntegral_prod_swap, setIntegral_prod _ hI]
    have hz : ∀ θ ∈ Ioo (-π) π, ∫ r in Ioo (0 : ℝ) R', Ar ((θ, r).swap) = -φ 0 := by
      intro θ _
      have hder : ∀ r : ℝ, HasDerivAt (fun r : ℝ => φ ((r : ℂ) * u θ)) (Ar (r, θ)) r := by
        intro r
        have hγ : HasDerivAt (fun r : ℝ => (r : ℂ) * u θ) (u θ) r := by
          simpa using ((hasDerivAt_id r).ofReal_comp).mul_const (u θ)
        exact (hdiff ((r : ℂ) * u θ)).hasFDerivAt.comp_hasDerivAt r hγ
      have hc : Continuous fun r : ℝ => Ar (r, θ) :=
        hArc.comp (Continuous.prodMk continuous_id continuous_const)
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hder r)
        (hc.intervalIntegrable 0 R')
      have hend : φ ((R' : ℂ) * u θ) = 0 := by
        apply hφout
        rw [norm_mul_u, abs_of_pos hR'pos]
        exact hRR'
      rw [hend, intervalIntegral.integral_of_le hR'pos.le, integral_Ioc_eq_integral_Ioo] at hftc
      simpa using hftc
    rw [setIntegral_congr_fun measurableSet_Ioo hz]
    simp
    left
    rw [max_eq_left (by positivity)]
    push_cast
    ring
  rw [hθ, hr]
  push_cast
  ring

end DbarKey

namespace HartogsGlue

variable {n : ℕ}

/-- Vanishing propagates along complex lines inside a ball. -/
theorem eqOn_zero_ball {f : (Fin n → ℂ) → ℂ} {z a : Fin n → ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z r)) (ha : a ∈ Metric.ball z r)
    (h0 : f =ᶠ[𝓝 a] 0) : EqOn f 0 (Metric.ball z r) := by
  intro w hw
  set φ : ℂ → (Fin n → ℂ) := fun t => a + t • (w - a) with hφ
  have hφd : Differentiable ℂ φ := by
    intro t
    simp only [hφ]
    fun_prop
  have hφc : Continuous φ := hφd.continuous
  set T : Set ℂ := φ ⁻¹' Metric.ball z r with hT
  have hTo : IsOpen T := Metric.isOpen_ball.preimage hφc
  have hTc : Convex ℝ T := by
    intro s hs t ht c d hc hd hcd
    simp only [hT, mem_preimage, hφ] at hs ht ⊢
    have hcv := (convex_ball z r) hs ht hc hd hcd
    convert hcv using 1
    have hcd' : (c : ℂ) + d = 1 := by exact_mod_cast hcd
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Pi.sub_apply]
    linear_combination (-(a i)) * hcd'
  have hg : DifferentiableOn ℂ (f ∘ φ) T := hf.comp hφd.differentiableOn (fun t ht => ht)
  have hga : AnalyticOnNhd ℂ (f ∘ φ) T := hg.analyticOnNhd hTo
  have h0T : (0 : ℂ) ∈ T := by simp [hT, hφ, ha]
  have h1T : (1 : ℂ) ∈ T := by simp [hT, hφ, hw]
  have hev : (f ∘ φ) =ᶠ[𝓝 0] 0 := by
    have htend : Tendsto φ (𝓝 0) (𝓝 a) := by
      have := hφc.tendsto 0
      simpa [hφ] using this
    filter_upwards [htend.eventually h0] with t ht
    simpa using ht
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero hTc.isPreconnected h0T hev h1T
  simpa [hφ] using this

/-- The real line `t ↦ update z k (z k + t v)` has velocity `Pi.single k v`. -/
theorem hasDerivAt_update_line (z : Fin n → ℂ) (k : Fin n) (v : ℂ) :
    HasDerivAt (fun t : ℝ => Function.update z k (z k + (t : ℂ) * v)) (Pi.single k v) 0 := by
  rw [hasDerivAt_pi]
  intro j
  by_cases h : j = k
  · subst h
    simp only [Function.update_self, Pi.single_eq_same]
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v).const_add (z j)
    simpa using this
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h]
    exact hasDerivAt_const _ _

theorem deriv_line_eq (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (k : Fin n) (v : ℂ)
    (hf : DifferentiableAt ℝ f z) :
    deriv (fun t : ℝ => f (Function.update z k (z k + (t : ℂ) * v))) 0 =
      fderiv ℝ f z (Pi.single k v) := by
  have hz : Function.update z k (z k + ((0 : ℝ) : ℂ) * v) = z := by simp
  have hf' : HasFDerivAt f (fderiv ℝ f z) (Function.update z k (z k + ((0 : ℝ) : ℂ) * v)) := by
    rw [hz]; exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_update_line z k v)).deriv

/-- `∂f/∂z̄_k` in terms of the real Fréchet derivative. -/
theorem wirtingerBar_eq_fderiv {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (k : Fin n)
    (hf : DifferentiableAt ℝ f z) :
    LeblSCV.Shared.wirtingerBar k f z = (1 / 2 : ℂ) *
      (fderiv ℝ f z (Pi.single k 1) + Complex.I * fderiv ℝ f z (Pi.single k Complex.I)) := by
  have h1 := deriv_line_eq f z k 1 hf
  have h2 := deriv_line_eq f z k Complex.I hf
  simp only [mul_one] at h1
  simp only [LeblSCV.Shared.wirtingerBar]
  rw [h1, h2]

theorem single_I_eq (k : Fin n) :
    (Pi.single k Complex.I : Fin n → ℂ) = Complex.I • (Pi.single k 1 : Fin n → ℂ) := by
  ext j
  by_cases hj : j = k
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/-- Holomorphic functions satisfy `∂f/∂z̄_k = 0`. -/
theorem wirtingerBar_eq_zero_of_differentiableAt {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f z) (k : Fin n) : LeblSCV.Shared.wirtingerBar k f z = 0 := by
  rw [wirtingerBar_eq_fderiv k (hf.restrictScalars ℝ), hf.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [single_I_eq k, map_smul, smul_eq_mul]
  linear_combination ((1 / 2 : ℂ) * fderiv ℂ f z (Pi.single k 1)) * Complex.I_sq

/-- G4 (Cauchy-Riemann): real differentiable with all `∂f/∂z̄_k = 0` implies complex differentiable. -/
theorem differentiableAt_of_wirtingerBar_eq_zero {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f z) (h : ∀ k, LeblSCV.Shared.wirtingerBar k f z = 0) :
    DifferentiableAt ℂ f z := by
  set L := fderiv ℝ f z with hL
  have hI : ∀ k, L (Pi.single k Complex.I) = Complex.I * L (Pi.single k 1) := by
    intro k
    have h0 := h k
    rw [wirtingerBar_eq_fderiv k hf] at h0
    have h2 : L (Pi.single k 1) + Complex.I * L (Pi.single k Complex.I) = 0 := by
      rcases mul_eq_zero.1 h0 with h3 | h3
      · norm_num at h3
      · exact h3
    linear_combination (-Complex.I) * h2 + (L (Pi.single k Complex.I)) * Complex.I_sq
  have hsingle : ∀ k (w : ℂ), L (Pi.single k w) = w * L (Pi.single k 1) := by
    intro k w
    have hw : (Pi.single k w : Fin n → ℂ) =
        w.re • (Pi.single k 1 : Fin n → ℂ) + w.im • (Pi.single k Complex.I : Fin n → ℂ) := by
      ext j
      by_cases hj : j = k
      · subst hj
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]
        exact (Complex.re_add_im w).symm
      · simp [Pi.single_eq_of_ne hj]
    rw [hw, map_add, map_smul, map_smul, hI k, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im w]
    ring
  let L' : (Fin n → ℂ) →L[ℂ] ℂ := ∑ k, (L (Pi.single k 1)) • ContinuousLinearMap.proj k
  have hLL : L'.restrictScalars ℝ = L := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.coe_restrictScalars']
    conv_rhs => rw [← Finset.univ_sum_single v]
    rw [map_sum, Finset.sum_congr rfl fun k _ => hsingle k (v k)]
    simp [L']
    all_goals (refine Finset.sum_congr rfl fun k _ => ?_; ring)
  exact (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hf.hasFDerivAt hLL).differentiableAt

theorem wirtingerBar_sub {h₁ h₂ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (k : Fin n)
    (h1 : DifferentiableAt ℝ h₁ z) (h2 : DifferentiableAt ℝ h₂ z) :
    LeblSCV.Shared.wirtingerBar k (fun w => h₁ w - h₂ w) z =
      LeblSCV.Shared.wirtingerBar k h₁ z - LeblSCV.Shared.wirtingerBar k h₂ z := by
  have hd : DifferentiableAt ℝ (fun w => h₁ w - h₂ w) z := h1.sub h2
  have hfd : fderiv ℝ (fun w => h₁ w - h₂ w) z = fderiv ℝ h₁ z - fderiv ℝ h₂ z :=
    (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv
  rw [wirtingerBar_eq_fderiv k hd, wirtingerBar_eq_fderiv k h1,
    wirtingerBar_eq_fderiv k h2, hfd]
  simp only [sub_apply]
  ring


end HartogsGlue

namespace DbarN

open HartogsGlue LeblSCV.Shared

variable {n : ℕ}

theorem inf_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem locInt_inv : LocallyIntegrable (fun w : ℂ => w⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num) ?_
    measurable_inv.aestronglyMeasurable
  refine Eventually.of_forall fun w => ?_
  rw [norm_inv, Real.rpow_neg_one, one_mul]

theorem int_ind (M R : ℝ) :
    Integrable (indicator (Metric.closedBall (0 : ℂ) R) fun w : ℂ => M * ‖w⁻¹‖) := by
  have h := (locInt_inv.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) R)).norm.const_mul M
  exact (show IntegrableOn (fun w : ℂ => M * ‖w⁻¹‖) (Metric.closedBall 0 R) volume from h).integrable_indicator
    measurableSet_closedBall

theorem integrable_K_mul {f : ℂ → ℂ} (hf : Continuous f) {R2 M : ℝ} (hM : ∀ w, ‖f w‖ ≤ M)
    (hfar : ∀ w : ℂ, R2 < ‖w‖ → f w = 0) : Integrable (fun w : ℂ => w⁻¹ * f w) := by
  refine Integrable.mono' (int_ind M R2)
    (measurable_inv.aestronglyMeasurable.mul hf.aestronglyMeasurable) (Eventually.of_forall fun w => ?_)
  by_cases hw : ‖w‖ ≤ R2
  · have hm : w ∈ Metric.closedBall (0 : ℂ) R2 := by rwa [Metric.mem_closedBall, dist_zero_right]
    rw [indicator_of_mem hm]
    show ‖w⁻¹ * f w‖ ≤ M * ‖w⁻¹‖
    rw [norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM w) (norm_nonneg _)
  · rw [hfar w (lt_of_not_ge hw), mul_zero, norm_zero]
    exact indicator_nonneg (fun w _ => mul_nonneg ((norm_nonneg _).trans (hM 0)) (norm_nonneg _)) w

noncomputable def e (j : Fin n) : Fin n → ℂ := Pi.single j 1

noncomputable def Psi (h : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  (1 / (π : ℂ)) * ∫ w : ℂ, w⁻¹ * h (z - w • e j)

theorem norm_le_of_coord {x : ℂ} (y z : Fin n → ℂ) (j : Fin n) (hy : y = z + x • e j) :
    ‖x‖ ≤ ‖y‖ + ‖z‖ := by
  have h1 : (y - z) j = x := by simp [hy, e]
  calc ‖x‖ = ‖(y - z) j‖ := by rw [h1]
    _ ≤ ‖y - z‖ := norm_le_pi_norm _ j
    _ ≤ ‖y‖ + ‖z‖ := norm_sub_le _ _

theorem eq_zero_of_far {h : (Fin n → ℂ) → ℂ} {R : ℝ} (hR : tsupport h ⊆ Metric.closedBall 0 R)
    {y : Fin n → ℂ} (hy : R < ‖y‖) : h y = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hm => ?_
  have := hR hm
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

theorem fderiv_eq_zero_of_far {h : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : tsupport h ⊆ Metric.closedBall 0 R) {y : Fin n → ℂ} (hy : R < ‖y‖) :
    fderiv ℝ h y = 0 := by
  by_contra hne
  have := hR (support_fderiv_subset ℝ hne)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

theorem contDiff_Psi {h : (Fin n → ℂ) → ℂ} (hh : ContDiff ℝ ∞ h) (hs : HasCompactSupport h)
    (j : Fin n) : ContDiff ℝ ∞ (Psi h j) := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  rw [contDiff_iff_contDiffAt]
  intro p0
  set G : (Fin n → ℂ) → ℂ → ℂ := fun p x => h (p + x • e j) with hG
  have hgs : ∀ p, ∀ x, p ∈ Metric.ball p0 1 → x ∉ Metric.closedBall (0 : ℂ) (R + ‖p0‖ + 1) →
      G p x = 0 := by
    intro p x hp hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    rw [Metric.mem_ball, dist_eq_norm] at hp
    apply eq_zero_of_far hR
    have h1 := norm_le_of_coord (x := x) (p + x • e j) p j rfl
    have h2 : ‖p‖ ≤ ‖p0‖ + ‖p - p0‖ := by
      calc ‖p‖ = ‖p0 + (p - p0)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (↿G) (Metric.ball p0 1 ×ˢ univ) := by
    apply ContDiff.contDiffOn
    exact hh.comp (contDiff_fst.add (contDiff_snd.smul contDiff_const))
  have hc := contDiffOn_convolution_right_with_param (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
    Metric.isOpen_ball (isCompact_closedBall (0 : ℂ) (R + ‖p0‖ + 1)) hgs locInt_inv hg
  have hca := hc.contDiffAt (x := (p0, (0 : ℂ)))
    (prod_mem_nhds (Metric.ball_mem_nhds p0 one_pos) univ_mem)
  have hcomp := hca.comp (f := fun z : Fin n → ℂ => (z, (0 : ℂ))) p0
    (contDiffAt_id.prodMk (contDiffAt_const (c := (0 : ℂ))))
  have heq : Psi h j = fun z => (1 / (π : ℂ)) *
      convolution (fun w : ℂ => w⁻¹) (G z) (ContinuousLinearMap.mul ℝ ℂ) volume 0 := by
    funext z
    simp only [Psi, convolution_def, ContinuousLinearMap.mul_apply', hG, zero_sub, neg_smul,
      ← sub_eq_add_neg]
  rw [heq]
  exact contDiffAt_const.mul hcomp

theorem fderiv_Psi_apply {h : (Fin n → ℂ) → ℂ} (hh : ContDiff ℝ ∞ h) (hs : HasCompactSupport h)
    (j : Fin n) (z d : Fin n → ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * fderiv ℝ h (z - w • e j) d) ∧
    fderiv ℝ (Psi h j) z d = (1 / (π : ℂ)) * ∫ w : ℂ, w⁻¹ * fderiv ℝ h (z - w • e j) d := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  have hd1 : Differentiable ℝ h := hh.differentiable inf_ne_zero
  have hDc : Continuous (fderiv ℝ h) := hh.continuous_fderiv inf_ne_zero
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support (hs.fderiv (𝕜 := ℝ))
  obtain ⟨M, hM⟩ := hh.continuous.bounded_above_of_compact_support hs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set R2 : ℝ := R + ‖z‖ + ‖d‖ + 1 with hR2
  set F : ℝ → ℂ → ℂ := fun t w => w⁻¹ * h (z + t • d - w • e j) with hF
  set F' : ℝ → ℂ → ℂ := fun t w => w⁻¹ * fderiv ℝ h (z + t • d - w • e j) d with hF'
  have hfar : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) 1 → ∀ w : ℂ, R2 < ‖w‖ →
      R < ‖z + t • d - w • e j‖ := by
    intro t ht w hw
    have h1 := norm_le_of_coord (x := -w) (z + t • d - w • e j) (z + t • d) j
      (by rw [neg_smul, ← sub_eq_add_neg])
    have ht' : |t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
    have h2 : ‖z + t • d‖ ≤ ‖z‖ + ‖d‖ := by
      calc ‖z + t • d‖ ≤ ‖z‖ + ‖t • d‖ := norm_add_le _ _
        _ = ‖z‖ + |t| * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖z‖ + ‖d‖ := by gcongr; exact mul_le_of_le_one_left (norm_nonneg d) ht'.le
    rw [norm_neg] at h1
    linarith
  have hbound : ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ w : ℂ,
      ‖F' t w‖ ≤ indicator (Metric.closedBall (0 : ℂ) R2) (fun w : ℂ => (C * ‖d‖) * ‖w⁻¹‖) w := by
    intro t ht w
    by_cases hw : ‖w‖ ≤ R2
    · have hm : w ∈ Metric.closedBall (0 : ℂ) R2 := by rwa [Metric.mem_closedBall, dist_zero_right]
      rw [indicator_of_mem hm]
      show ‖w⁻¹ * fderiv ℝ h (z + t • d - w • e j) d‖ ≤ C * ‖d‖ * ‖w⁻¹‖
      rw [norm_mul, mul_comm (C * ‖d‖)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact ((fderiv ℝ h _).le_opNorm d).trans
        (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg d))
    · have hz := fderiv_eq_zero_of_far hR (hfar t ht w (lt_of_not_ge hw))
      have : F' t w = 0 := by simp only [hF', hz, zero_apply, mul_zero]
      rw [this, norm_zero]
      exact indicator_nonneg (fun w _ => mul_nonneg (mul_nonneg hC0 (norm_nonneg _))
        (norm_nonneg _)) w
  have hdiffF : ∀ w : ℂ, ∀ t : ℝ, HasDerivAt (fun t => F t w) (F' t w) t := by
    intro w t
    have hl : HasDerivAt (fun t : ℝ => z + t • d - w • e j) d t := by
      simpa using (((hasDerivAt_id t).smul_const d).const_add z).sub_const (w • e j)
    exact ((hd1 _).hasFDerivAt.comp_hasDerivAt t hl).const_mul w⁻¹
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) volume :=
    Eventually.of_forall fun t => measurable_inv.aestronglyMeasurable.mul
      (hh.continuous.comp (by fun_prop : Continuous fun w : ℂ => z + t • d - w • e j)).aestronglyMeasurable
  have hF_int : Integrable (F 0) :=
    integrable_K_mul (f := fun w => h (z + (0 : ℝ) • d - w • e j))
      (hh.continuous.comp (by fun_prop)) (R2 := R2) (fun w => hM _)
      (fun w hw => eq_zero_of_far hR (hfar 0 (Metric.mem_ball_self one_pos) w hw))
  have hF'_meas : AEStronglyMeasurable (F' 0) volume :=
    measurable_inv.aestronglyMeasurable.mul
      ((hDc.comp (by fun_prop : Continuous fun w : ℂ => z + (0 : ℝ) • d - w • e j)).clm_apply
        continuous_const).aestronglyMeasurable
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (Metric.ball_mem_nhds 0 one_pos) hF_meas hF_int hF'_meas
    (Eventually.of_forall fun w t ht => hbound t ht w) (int_ind (C * ‖d‖) R2)
    (Eventually.of_forall fun w t _ => hdiffF w t)
  have hPsiD : DifferentiableAt ℝ (Psi h j) z := (contDiff_Psi hh hs j).differentiable inf_ne_zero z
  have hl : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have hP : HasFDerivAt (Psi h j) (fderiv ℝ (Psi h j) z) (z + (0 : ℝ) • d) := by
    simpa using hPsiD.hasFDerivAt
  have H1 := hP.comp_hasDerivAt (0 : ℝ) hl
  have H2 : HasDerivAt (fun t : ℝ => (1 / (π : ℂ)) * ∫ w, F t w) ((1 / (π : ℂ)) * ∫ w, F' 0 w) 0 :=
    hmain.2.const_mul _
  have H3 := H1.unique H2
  have hF'0 : F' 0 = fun w : ℂ => w⁻¹ * fderiv ℝ h (z - w • e j) d := by
    funext w; simp [hF']
  rw [hF'0] at H3 hmain
  exact ⟨hmain.1, H3⟩

theorem wirtingerBar_Psi {h : (Fin n → ℂ) → ℂ} (hh : ContDiff ℝ ∞ h) (hs : HasCompactSupport h)
    (j k : Fin n) (z : Fin n → ℂ) :
    wirtingerBar k (Psi h j) z = (1 / (π : ℂ)) * ∫ w : ℂ, w⁻¹ * wirtingerBar k h (z - w • e j) := by
  have hPsiD : DifferentiableAt ℝ (Psi h j) z := (contDiff_Psi hh hs j).differentiable inf_ne_zero z
  have hd1 : Differentiable ℝ h := hh.differentiable inf_ne_zero
  obtain ⟨i1, e1⟩ := fderiv_Psi_apply hh hs j z (Pi.single k 1)
  obtain ⟨i2, e2⟩ := fderiv_Psi_apply hh hs j z (Pi.single k I)
  rw [wirtingerBar_eq_fderiv k hPsiD, e1, e2]
  have hcongr : (fun w : ℂ => w⁻¹ * wirtingerBar k h (z - w • e j)) =
      fun w => (1 / 2 : ℂ) * (w⁻¹ * fderiv ℝ h (z - w • e j) (Pi.single k 1)) +
        ((1 / 2 : ℂ) * I) * (w⁻¹ * fderiv ℝ h (z - w • e j) (Pi.single k I)) := by
    funext w
    rw [wirtingerBar_eq_fderiv k (hd1 _)]
    ring
  rw [hcongr, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  ring

theorem fderiv_line {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℝ f) (z : Fin n → ℂ) (j : Fin n)
    (x v : ℂ) : fderiv ℝ (fun x : ℂ => f (z + x • e j)) x v = fderiv ℝ f (z + x • e j) (v • e j) := by
  have hl : HasFDerivAt (fun x : ℂ => z + x • e j)
      ((ContinuousLinearMap.id ℝ ℂ).smulRight (e j)) x :=
    ((hasFDerivAt_id x).smul_const (e j)).const_add z
  have hc := (hf (z + x • e j)).hasFDerivAt.comp x hl
  rw [show (fun x : ℂ => f (z + x • e j)) = f ∘ fun x => z + x • e j from rfl, hc.fderiv]
  simp

theorem Psi_dbar (g : Fin n → (Fin n → ℂ) → ℂ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hs : ∀ j, HasCompactSupport (g j))
    (hcompat : ∀ k l : Fin n, wirtingerBar l (g k) = wirtingerBar k (g l)) (j k : Fin n)
    (z : Fin n → ℂ) : wirtingerBar k (Psi (g j) j) z = g k z := by
  rw [wirtingerBar_Psi (hg j) (hs j) j k z, hcompat j k]
  set φ : ℂ → ℂ := fun x => g k (z + x • e j) with hφ
  have hd1 : Differentiable ℝ (g k) := (hg k).differentiable inf_ne_zero
  have hφC : ContDiff ℝ 1 φ := by
    have := (hg k).comp (contDiff_const.add (contDiff_id.smul contDiff_const) :
      ContDiff ℝ ∞ fun x : ℂ => z + x • e j)
    exact this.of_le (by exact_mod_cast le_top)
  obtain ⟨R, hR⟩ := (hs k).isCompact.isBounded.subset_closedBall 0
  have hφS : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + ‖z‖)) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    apply eq_zero_of_far hR
    have := norm_le_of_coord (x := x) (z + x • e j) z j rfl
    linarith
  have hdb : ∀ x, DbarKey.dbar1 φ x = wirtingerBar j (g k) (z + x • e j) := by
    intro x
    rw [wirtingerBar_eq_fderiv j (hd1 _), DbarKey.dbar1, hφ, fderiv_line hd1, fderiv_line hd1,
      one_smul, single_I_eq]
    rfl
  have hkey := DbarKey.key φ hφC hφS
  have hint : ∫ w : ℂ, w⁻¹ * wirtingerBar j (g k) (z - w • e j) = -∫ w : ℂ, DbarKey.dbar1 φ w / w := by
    rw [← integral_neg, ← integral_neg_eq_self (fun w : ℂ => -(DbarKey.dbar1 φ w / w))]
    congr 1
    funext w
    rw [hdb, div_neg, neg_neg, div_eq_inv_mul, neg_smul, ← sub_eq_add_neg]
  rw [hint, hkey]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [hφ, zero_smul, add_zero]
  field_simp

theorem Psi_far {h : (Fin n → ℂ) → ℂ} {R : ℝ} (hR : tsupport h ⊆ Metric.closedBall 0 R)
    (j i : Fin n) (hij : i ≠ j) (z : Fin n → ℂ) (hz : R < ‖z i‖) : Psi h j z = 0 := by
  have : ∀ w : ℂ, w⁻¹ * h (z - w • e j) = 0 := by
    intro w
    rw [eq_zero_of_far hR, mul_zero]
    calc R < ‖z i‖ := hz
      _ = ‖(z - w • e j) i‖ := by simp [e, Pi.single_eq_of_ne hij]
      _ ≤ ‖z - w • e j‖ := norm_le_pi_norm _ i
  simp [Psi, this]

theorem entire_zero {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) {a : Fin n → ℂ}
    (h0 : f =ᶠ[𝓝 a] 0) : f = 0 := by
  funext w
  have := eqOn_zero_ball (z := a) (r := ‖w - a‖ + 1) hf.differentiableOn
    (Metric.mem_ball_self (by positivity)) h0
  exact this (by rw [Metric.mem_ball, dist_eq_norm]; linarith)

theorem differentiable_of_dbar_zero {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : ∀ k z, wirtingerBar k f z = 0) : Differentiable ℂ f := fun z =>
  differentiableAt_of_wirtingerBar_eq_zero (hf.differentiable inf_ne_zero z) (fun k => h k z)

end DbarN

open DbarN HartogsGlue

open scoped ContDiff in
theorem solution {n : ℕ} (hn : 2 ≤ n) (g : Fin n → (Fin n → ℂ) → ℂ)
    (hg_smooth : ∀ j, ContDiff ℝ ∞ (g j))
    (hg_supp : ∀ j, HasCompactSupport (g j))
    (hcompat : ∀ k l : Fin n, LeblSCV.Shared.wirtingerBar l (g k) = LeblSCV.Shared.wirtingerBar k (g l)) :
    ∃! ψ : (Fin n → ℂ) → ℂ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ ∀ k : Fin n, LeblSCV.Shared.wirtingerBar k ψ = g k := by
  obtain ⟨R, hR⟩ : ∃ R, ⋃ j, tsupport (g j) ⊆ Metric.closedBall 0 R :=
    (isCompact_iUnion fun j => hg_supp j).isBounded.subset_closedBall 0
  have hRj : ∀ j, tsupport (g j) ⊆ Metric.closedBall 0 R := fun j => (subset_iUnion _ j).trans hR
  let j0 : Fin n := ⟨0, by omega⟩
  let j1 : Fin n := ⟨1, by omega⟩
  have hj : j1 ≠ j0 := by simp [j0, j1, Fin.ext_iff]
  have hdiff : ∀ j, ContDiff ℝ ∞ (Psi (g j) j) := fun j => contDiff_Psi (hg_smooth j) (hg_supp j) j
  have hdb : ∀ j k z, LeblSCV.Shared.wirtingerBar k (Psi (g j) j) z = g k z :=
    Psi_dbar g hg_smooth hg_supp hcompat
  have hagree : Psi (g j0) j0 = Psi (g j1) j1 := by
    set H : (Fin n → ℂ) → ℂ := fun z => Psi (g j0) j0 z - Psi (g j1) j1 z with hH
    have hHs : ContDiff ℝ ∞ H := (hdiff j0).sub (hdiff j1)
    have hHd : Differentiable ℂ H := differentiable_of_dbar_zero hHs (fun k z => by
      rw [hH, wirtingerBar_sub k ((hdiff j0).differentiable inf_ne_zero z)
        ((hdiff j1).differentiable inf_ne_zero z), hdb, hdb, sub_self])
    have hn1 : R < ‖((R + 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith [le_abs_self (R + 1)]
    have hopen : IsOpen {z : Fin n → ℂ | R < ‖z j0‖ ∧ R < ‖z j1‖} :=
      (isOpen_lt continuous_const (continuous_apply j0).norm).inter
        (isOpen_lt continuous_const (continuous_apply j1).norm)
    have h0 : H =ᶠ[𝓝 (fun _ => ((R + 1 : ℝ) : ℂ))] 0 := by
      filter_upwards [hopen.mem_nhds ⟨hn1, hn1⟩] with z hz
      simp only [hH, Pi.zero_apply]
      rw [Psi_far (hRj j0) j0 j1 hj z hz.2, Psi_far (hRj j1) j1 j0 hj.symm z hz.1, sub_self]
    have h1 := congrFun (entire_zero hHd h0)
    funext z
    have h2 := h1 z
    simp only [hH, Pi.zero_apply] at h2
    exact sub_eq_zero.1 h2
  have hsupp : HasCompactSupport (Psi (g j0) j0) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℂ) R) fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    obtain ⟨i, hi⟩ : ∃ i, R < ‖z i‖ := by
      by_contra hcon
      push_neg at hcon
      have hR0 : 0 ≤ R := (norm_nonneg _).trans (hcon j0)
      exact absurd ((pi_norm_le_iff_of_nonneg hR0).2 hcon) (not_le.2 hz)
    by_cases hi0 : i = j0
    · rw [hagree]
      exact Psi_far (hRj j1) j1 i (by rw [hi0]; exact hj.symm) z hi
    · exact Psi_far (hRj j0) j0 i hi0 z hi
  refine ⟨Psi (g j0) j0, ⟨hdiff j0, hsupp, fun k => funext (hdb j0 k)⟩, ?_⟩
  rintro ψ ⟨h1, h2, h3⟩
  set H : (Fin n → ℂ) → ℂ := fun z => ψ z - Psi (g j0) j0 z with hH
  have hHs : ContDiff ℝ ∞ H := h1.sub (hdiff j0)
  have hHd : Differentiable ℂ H := differentiable_of_dbar_zero hHs (fun k z => by
    rw [hH, wirtingerBar_sub k (h1.differentiable inf_ne_zero z)
      ((hdiff j0).differentiable inf_ne_zero z), h3, hdb, sub_self])
  have hHsupp : HasCompactSupport H := h2.sub hsupp
  obtain ⟨R3, hR3⟩ := hHsupp.isCompact.isBounded.subset_closedBall 0
  set a : Fin n → ℂ := fun _ => ((|R3| + 1 : ℝ) : ℂ) with ha
  have haR : R3 < ‖a‖ := by
    have := norm_le_pi_norm a j0
    have h4 : ‖a j0‖ = |R3| + 1 := by
      simp only [ha, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    linarith [le_abs_self R3]
  have hopen : IsOpen {z : Fin n → ℂ | R3 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have h0 : H =ᶠ[𝓝 a] 0 := by
    filter_upwards [hopen.mem_nhds haR] with z hz
    exact eq_zero_of_far hR3 hz
  have h5 := congrFun (entire_zero hHd h0)
  funext z
  have h6 := h5 z
  simp only [hH, Pi.zero_apply] at h6
  exact sub_eq_zero.1 h6
