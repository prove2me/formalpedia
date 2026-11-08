-- Prove2me | solution 1 for NonStrongConvexGM.QuasiStrong.quasi_strong_implies_gradient_growth
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:42:23.418624+00:00
-- url     : https://prove2.me/submissions/aa77feb4-ec63-4acc-a3b6-0a3e3cd2cc3f

import Definitions.Def_NonStrongConvexGM_QuasiStrong_Model

namespace Aux_QSGG
open NonStrongConvexGM.QuasiStrong NecoaraNG.Chain Filter Topology

variable {n : ℕ}

theorem opt_convex (P : Problem n) : Convex ℝ (optSet P.X P.f) := by
  intro x hx y hy a b ha hb hab
  refine ⟨P.convex.1 hx.1 hy.1 ha hb hab, fun w hw => ?_⟩
  have h := P.convex.2 hx.1 hy.1 ha hb hab
  have h1 := mul_le_mul_of_nonneg_left (hx.2 w hw) ha
  have h2 := mul_le_mul_of_nonneg_left (hy.2 w hw) hb
  have e : a * P.f w + b * P.f w = P.f w := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul] at h
  linarith

theorem opt_closed (P : Problem n) : IsClosed (optSet P.X P.f) := by
  obtain ⟨x0, hx0⟩ := P.attained
  have hc : ContinuousOn P.f P.X := fun x hx => (P.derivative x hx).continuousWithinAt
  have : optSet P.X P.f = P.X ∩ P.f ⁻¹' Set.Iic (P.f x0) := by
    ext x
    simp only [optSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, h x0 hx0.1⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, fun y hy => h.trans (hx0.2 y hy)⟩
  rw [this]; exact hc.preimage_isClosed_of_isClosed P.closed isClosed_Iic

theorem bdd (K : Set (E n)) (u : E n) : BddBelow (Set.range fun w : K => ‖u - (w : E n)‖) :=
  ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩

theorem nearest_iff (P : Problem n) (u p : E n) (hp : p ∈ optSet P.X P.f) :
    IsNearest (optSet P.X P.f) u p ↔ ∀ w ∈ optSet P.X P.f, inner ℝ (u - p) (w - p) ≤ 0 := by
  rw [← norm_eq_iInf_iff_real_inner_le_zero (opt_convex P) hp]
  haveI : Nonempty (optSet P.X P.f) := ⟨⟨p, hp⟩⟩
  constructor
  · rintro ⟨_, h⟩
    apply le_antisymm
    · exact le_ciInf (fun w => h w.1 w.2)
    · exact ciInf_le (bdd _ u) ⟨p, hp⟩
  · intro h
    refine ⟨hp, fun z hz => ?_⟩
    rw [h]
    exact ciInf_le (bdd _ u) ⟨z, hz⟩

theorem exists_nearest (P : Problem n) (u : E n) : ∃ p, IsNearest (optSet P.X P.f) u p := by
  obtain ⟨v, hv, h⟩ := exists_norm_eq_iInf_of_complete_convex P.attained
    (opt_closed P).isComplete (opt_convex P) u
  exact ⟨v, hv, fun z hz => by rw [h]; exact ciInf_le (bdd _ u) ⟨z, hz⟩⟩

theorem nearest_unique (P : Problem n) (u p q : E n) (hp : IsNearest (optSet P.X P.f) u p)
    (hq : IsNearest (optSet P.X P.f) u q) : p = q := by
  have h1 := (nearest_iff P u p hp.1).mp hp q hq.1
  have h2 := (nearest_iff P u q hq.1).mp hq p hp.1
  have e : inner ℝ (u - p) (q - p) + inner ℝ (u - q) (p - q) = ‖q - p‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have : p - q = -(q - p) := by abel
    rw [this, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
    congr 1; abel
  have h0 : ‖q - p‖ = 0 := by nlinarith [norm_nonneg (q - p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

theorem nearestOpt_spec (P : Problem n) (u : E n) :
    IsNearest (optSet P.X P.f) u (nearestOpt P u) := by
  unfold nearestOpt project
  rw [dif_pos (exists_nearest P u)]
  exact Classical.choose_spec (exists_nearest P u)

theorem nearestOpt_eq (P : Problem n) (u p : E n) (hp : IsNearest (optSet P.X P.f) u p) :
    nearestOpt P u = p :=
  nearest_unique P u _ _ (nearestOpt_spec P u) hp

theorem under (P : Problem n) (κ : ℝ) (h : IsQuasiStrong P κ) (x : E n) (hx : x ∈ P.X) :
    value P + inner ℝ (P.grad (nearestOpt P x)) (x - nearestOpt P x) +
      κ / 2 * ‖x - nearestOpt P x‖ ^ 2 ≤ P.f x := by
  obtain ⟨xb, hxb⟩ : ∃ xb, xb = nearestOpt P x := ⟨_, rfl⟩
  rw [← hxb]
  have hnear : IsNearest (optSet P.X P.f) x xb := hxb ▸ nearestOpt_spec P x
  have hxbX : xb ∈ P.X := hnear.1.1
  obtain ⟨v, hv⟩ : ∃ v, v = x - xb := ⟨_, rfl⟩
  rw [← hv]
  obtain ⟨d, hd⟩ : ∃ d, d = ‖v‖ := ⟨_, rfl⟩
  rw [← hd]
  have hxv : xb + v = x := by rw [hv]; abel
  have hγX : ∀ τ ∈ Set.Icc (0 : ℝ) 1, xb + τ • v ∈ P.X := fun τ hτ => by
    rw [hv]; exact P.convex.1.add_smul_sub_mem hxbX hx hτ
  have hγnear : ∀ τ : ℝ, 0 ≤ τ → nearestOpt P (xb + τ • v) = xb := by
    intro τ hτ
    apply nearestOpt_eq
    rw [nearest_iff P _ _ hnear.1]
    intro w hw
    have := (nearest_iff P x xb hnear.1).mp hnear w hw
    rw [show xb + τ • v - xb = τ • v by abel, real_inner_smul_left, hv]
    exact mul_nonpos_of_nonneg_of_nonpos hτ this
  have hfxb : P.f xb = value P := by
    unfold value
    have h0 := Classical.choose_spec P.attained
    exact le_antisymm (hnear.1.2 _ h0.1) (h0.2 _ hnear.1.1)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun τ => P.f (xb + τ • v) - value P := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, D = fun τ => inner ℝ (P.grad (xb + τ • v)) v := ⟨_, rfl⟩
  have hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (D τ) (Set.Icc 0 1) τ := by
    intro τ hτ
    have hγd : HasDerivAt (fun s : ℝ => xb + s • v) v τ := by
      have := ((hasDerivAt_id τ).smul_const v).const_add xb
      rw [one_smul] at this
      exact this
    have h1 := (P.derivative (xb + τ • v) (hγX τ hτ)).comp_hasDerivWithinAt τ
      hγd.hasDerivWithinAt (fun s hs => hγX s hs)
    have h2 := h1.sub_const (value P)
    rw [hφ, hD]
    exact h2.congr_deriv (by first | rfl | simp [innerSL_apply])
  have hφ0 : φ 0 = 0 := by rw [hφ]; simp [hfxb]
  have hQS : ∀ τ ∈ Set.Icc (0 : ℝ) 1, φ τ ≤ τ * D τ - κ / 2 * τ ^ 2 * d ^ 2 := by
    intro τ hτ
    have := h.2 (xb + τ • v) (hγX τ hτ)
    rw [hγnear τ hτ.1] at this
    rw [show xb - (xb + τ • v) = -(τ • v) by abel, show xb + τ • v - xb = τ • v by abel,
      inner_neg_right, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hτ.1] at this
    rw [hφ, hD]
    simp only
    rw [hd]
    have e : (τ * ‖v‖) ^ 2 = τ ^ 2 * ‖v‖ ^ 2 := by ring
    rw [e] at this
    linarith
  -- ψ
  have hφc : ContinuousOn φ (Set.Icc 0 1) := fun τ hτ => (hderiv τ hτ).continuousWithinAt
  have hmono : MonotoneOn (fun τ => φ τ / τ - κ / 2 * d ^ 2 * τ) (Set.Ioc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1)
      (f' := fun τ => (D τ * τ - φ τ * 1) / τ ^ 2 - κ / 2 * d ^ 2 * 1)
    · apply ContinuousOn.sub
      · apply ContinuousOn.div (hφc.mono Set.Ioc_subset_Icc_self) continuousOn_id
        intro τ hτ; exact hτ.1.ne'
      · exact continuousOn_const.mul continuousOn_id
    · intro τ hτ
      rw [interior_Ioc] at hτ
      have hφd : HasDerivAt φ (D τ) τ :=
        (hderiv τ ⟨hτ.1.le, hτ.2.le⟩).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
      have := (hφd.div (hasDerivAt_id τ) hτ.1.ne').sub ((hasDerivAt_id τ).const_mul (κ / 2 * d ^ 2))
      exact this.hasDerivWithinAt
    · intro τ hτ
      rw [interior_Ioc] at hτ
      have hq := hQS τ ⟨hτ.1.le, hτ.2.le⟩
      have hτ2 : 0 < τ ^ 2 := pow_pos hτ.1 2
      simp only [id, mul_one]
      rw [sub_nonneg, le_div_iff₀ hτ2]
      nlinarith
  have hT := hasDerivWithinAt_iff_tendsto_slope.mp (hderiv 0 ⟨le_refl _, zero_le_one⟩)
  rw [Set.Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT zero_lt_one] at hT
  have hT2 : Tendsto (fun τ => slope φ 0 τ - κ / 2 * d ^ 2 * τ) (𝓝[>] 0)
      (𝓝 (D 0 - κ / 2 * d ^ 2 * 0)) :=
    hT.sub (((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), slope φ 0 τ - κ / 2 * d ^ 2 * τ ≤
      φ 1 / 1 - κ / 2 * d ^ 2 * 1 := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with τ hτ
    rw [slope_def_field, hφ0, sub_zero, sub_zero]
    exact hmono ⟨hτ.1, hτ.2.le⟩ ⟨zero_lt_one, le_refl _⟩ hτ.2.le
  have hfin := le_of_tendsto hT2 hev
  rw [hφ, hD] at hfin
  simp only [zero_smul, add_zero, one_smul, div_one, mul_zero, sub_zero, mul_one] at hfin
  rw [hxv] at hfin
  linarith

end Aux_QSGG

open NonStrongConvexGM.QuasiStrong Aux_QSGG in
theorem solution {n : ℕ} (P : Problem n) (κ : ℝ) (h : IsQuasiStrong P κ) :
    GradientGrowth P κ := by
  refine ⟨h.1, fun x hx => ?_⟩
  have h1 := h.2 x hx
  have h2 := under P κ h x hx
  rw [inner_sub_left]
  have e : inner ℝ (P.grad x) (nearestOpt P x - x) = -inner ℝ (P.grad x) (x - nearestOpt P x) := by
    rw [← inner_neg_right, neg_sub]
  rw [e] at h1
  linarith
