-- Prove2me | solution 1 for HubbleLaw.recession_velocity_eq_hubbleParameter_mul_properDistance
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:41:29.026889+00:00
-- url     : https://prove2.me/submissions/d88564fb-0b1e-434f-b6e7-e974ce3d280f

import Definitions.Def_HubbleLawDefs

open HubbleLaw

theorem H_comoving (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t) (hat : a t ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (properPosition a x) (hubbleParameter a t • properPosition a x t) t := by
  unfold properPosition hubbleParameter
  rw [smul_smul, div_mul_cancel₀ _ hat]
  exact ha.hasDerivAt.smul_const x

theorem H_recession (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t) (hat : 0 < a t)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (properDistance a x y)
      (hubbleParameter a t * properDistance a x y t) t := by
  have hd : ∀ s, 0 < a s → properDistance a x y s = a s * ‖x - y‖ := by
    intro s hs
    unfold properDistance properPosition
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hev : properDistance a x y =ᶠ[nhds t] fun s => a s * ‖x - y‖ := by
    filter_upwards [ha.continuousAt.eventually (Ioi_mem_nhds hat)] with s hs
    exact hd s hs
  have hder : HasDerivAt (fun s => a s * ‖x - y‖) (deriv a t * ‖x - y‖) t :=
    ha.hasDerivAt.mul_const _
  rw [hd t hat]
  unfold hubbleParameter
  rw [show deriv a t / a t * (a t * ‖x - y‖) = deriv a t * ‖x - y‖ by field_simp]
  exact hder.congr_of_eventuallyEq hev

theorem H_idealized (H t : ℝ) (hH : 0 ≤ H)
    (p q : ℝ → EuclideanSpace ℝ (Fin 3))
    (hp : HasDerivAt p (H • p t) t) (hq : HasDerivAt q (H • q t) t) :
    HasDerivAt (fun s => p s - q s) (H • (p t - q t)) t ∧
      ‖H • (p t - q t)‖ = H * ‖p t - q t‖ := by
  refine ⟨?_, ?_⟩
  · rw [smul_sub]; exact hp.sub hq
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hH]

theorem H_redshift (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : DifferentiableAt ℝ a t₀) (h0 : 0 < a t₀) :
    Filter.Tendsto (fun te => (a t₀ / a te - 1) / (t₀ - te)) (nhdsWithin t₀ {t₀}ᶜ)
      (nhds (hubbleParameter a t₀)) := by
  have h1 := hasDerivAt_iff_tendsto_slope.1 ha.hasDerivAt
  have h2 : Filter.Tendsto a (nhdsWithin t₀ {t₀}ᶜ) (nhds (a t₀)) :=
    ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h3 := h1.div h2 h0.ne'
  unfold hubbleParameter
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin, h2.eventually_ne h0.ne'] with te hte hne
  have hte' : te - t₀ ≠ 0 := sub_ne_zero.2 hte
  have hte'' : t₀ - te ≠ 0 := sub_ne_zero.2 (Ne.symm hte)
  show slope a t₀ te / a te = _
  rw [slope_def_field]
  field_simp
  ring

theorem H_exp (a : ℝ → ℝ) (H₀ t₀ : ℝ) (ha : Differentiable ℝ a) (hpos : ∀ s, 0 < a s)
    (hH : ∀ s, hubbleParameter a s = H₀) :
    ∀ t, a t = a t₀ * Real.exp (H₀ * (t - t₀)) := by
  have hd : ∀ s, deriv a s = H₀ * a s := by
    intro s
    have := hH s
    unfold hubbleParameter at this
    rw [← this]; field_simp [(hpos s).ne']
  set g : ℝ → ℝ := fun s => a s * Real.exp (-(H₀ * (s - t₀))) with hg
  have hgd : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => -(H₀ * (s - t₀))) (-(H₀ * 1)) s :=
      (((hasDerivAt_id s).sub_const t₀).const_mul H₀).neg
    have h2 := (ha s).hasDerivAt.mul h1.exp
    refine h2.congr_deriv ?_
    rw [hd]; ring
  intro t
  have hc := is_const_of_deriv_eq_zero (fun s => (hgd s).differentiableAt) (fun s => (hgd s).deriv) t t₀
  simp only [hg, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at hc
  rw [← hc, mul_assoc, ← Real.exp_add]
  simp

theorem H_deriv (a : ℝ → ℝ) (t : ℝ) (ha : ContDiff ℝ 2 a)
    (hpos : ∀ s, 0 < a s) (hd : deriv a t ≠ 0) :
    HasDerivAt (hubbleParameter a)
      (-(1 + decelerationParameter a t) * hubbleParameter a t ^ 2) t := by
  have h1 : HasDerivAt a (deriv a t) t := ((ha.differentiable (by norm_num)) t).hasDerivAt
  have h2 : HasDerivAt (deriv a) (deriv (deriv a) t) t :=
    (((ha.iterate_deriv' 1 1).differentiable one_ne_zero) t).hasDerivAt
  have h3 := h2.div h1 (hpos t).ne'
  refine (h3 : HasDerivAt (hubbleParameter a) _ t).congr_deriv ?_
  unfold hubbleParameter decelerationParameter
  have := (hpos t).ne'
  field_simp
  ring

theorem H_inv_time (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a)
    (h0 : a 0 = 0) (hpos : ∀ s, 0 < s → 0 < a s) (hd : ∀ s, 0 < s → deriv a s ≠ 0)
    (hq : ∀ s, 0 < s → decelerationParameter a s = 0) :
    ∀ t, 0 < t → hubbleParameter a t = 1 / t := by
  intro t ht
  have hda : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv a) := (ha.iterate_deriv' 1 1).differentiable one_ne_zero
  have h2 : ∀ s, 0 < s → deriv (deriv a) s = 0 := by
    intro s hs
    have h := hq s hs
    unfold decelerationParameter at h
    have hne := hd s hs
    have hp := (hpos s hs).ne'
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · rw [neg_eq_zero, mul_eq_zero] at h
      exact h.resolve_right hp
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) hne
  set c := deriv a t with hc
  have hconst : ∀ s, 0 < s → deriv a s = c := fun s hs =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdd.differentiableOn
      (fun x hx => h2 x hx) hs ht
  -- `a s - c s` is constant on `(0, ∞)`
  set g : ℝ → ℝ := fun s => a s - c * s with hg
  have hgd : Differentiable ℝ g := hda.sub ((differentiable_id).const_mul c)
  have hg' : Set.EqOn (deriv g) 0 (Set.Ioi 0) := by
    intro s hs
    have : HasDerivAt g (deriv a s - c * 1) s :=
      (hda s).hasDerivAt.sub ((hasDerivAt_id s).const_mul c)
    rw [this.deriv, hconst s hs]; simp
  obtain ⟨K, hK⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    hgd.differentiableOn hg'
  have hK0 : K = 0 := by
    have hlim : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
      hgd.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds K) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (hK s hs).symm)
    have := tendsto_nhds_unique hlim2 hlim
    rw [this]; simp [hg, h0]
  have hat : a t = c * t := by
    have := hK t ht
    rw [hK0] at this
    simp only [hg] at this
    linarith
  unfold hubbleParameter
  rw [hat, ← hc]
  have hc0 : c ≠ 0 := hd t ht
  field_simp

theorem solution
    (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t) (hat : 0 < a t)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (properDistance a x y)
      (hubbleParameter a t * properDistance a x y t) t := by
  apply H_recession <;> assumption
