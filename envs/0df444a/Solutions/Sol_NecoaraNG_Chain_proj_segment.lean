-- Prove2me | solution 1 for NecoaraNG.Chain.proj_segment
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:35:10.010481+00:00
-- url     : https://prove2.me/submissions/7a73ab06-1f7e-4222-a213-a76b7d4de9de

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

set_option autoImplicit false
open scoped InnerProductSpace

section NGSec
open NecoaraNG.Chain Filter Topology

namespace NGP
variable {n : ℕ}

theorem inner_grad_eq (f : E n → ℝ) (p v : E n) : ⟪gradient f p, v⟫_ℝ = fderiv ℝ f p v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem line_mem {X : Set (E n)} (hX : Convex ℝ X) {x y : E n} (hx : x ∈ X) (hy : y ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ X := by
  have := hX hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  convert this using 1
  module

theorem line_hasDeriv {f : E n → ℝ} {p : E n} (hp : DifferentiableAt ℝ f p) (x v : E n) (t : ℝ)
    (hpt : x + t • v = p) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (⟪gradient f p, v⟫_ℝ) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  rw [inner_grad_eq]
  subst hpt
  exact hp.hasFDerivAt.comp_hasDerivAt t h1

theorem nearest_seg {S : Set (E n)} {x xb : E n} (hb : IsNearest S x xb) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : IsNearest S (xb + t • (x - xb)) xb := by
  refine ⟨hb.1, fun z hz => ?_⟩
  have e1 : xb + t • (x - xb) - xb = t • (x - xb) := by abel
  have e2 : x - (xb + t • (x - xb)) = (1 - t) • (x - xb) := by module
  have n1 : ‖xb + t • (x - xb) - xb‖ = t * ‖x - xb‖ := by
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have n2 : ‖x - (xb + t • (x - xb))‖ = (1 - t) * ‖x - xb‖ := by
    rw [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  have h1 : ‖x - z‖ ≤ ‖x - (xb + t • (x - xb))‖ + ‖(xb + t • (x - xb)) - z‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h2 : ‖x - xb‖ ≤ ‖x - z‖ := hb.2 z hz
  rw [n1]
  rw [n2] at h1
  nlinarith

theorem slope_tendsto {f : E n → ℝ} {xb : E n} (hp : DifferentiableAt ℝ f xb) (v : E n) :
    Tendsto (fun ε : ℝ => (f (xb + ε • v) - f xb) / ε) (𝓝[>] 0) (𝓝 ⟪gradient f xb, v⟫_ℝ) := by
  have h1 := line_hasDeriv hp xb v 0 (by simp)
  have h2 := h1.tendsto_slope_zero_right
  refine h2.congr (fun ε => ?_)
  simp only [smul_eq_mul, zero_add, zero_smul, add_zero]
  rw [div_eq_inv_mul]

theorem qs_under {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {κ : ℝ} (hqs : QuasiStrong X f κ) :
    QuadUnder X f κ := by
  intro x hx xb hb
  have hxb : xb ∈ X := hb.1.1
  set v := x - xb with hv
  set r := ‖v‖ with hr
  let φ : ℝ → ℝ := fun t => f (xb + t • v) - f xb
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, xb + t • v ∈ X := fun t ht => line_mem hX hxb hx ht
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (⟪gradient f (xb + t • v), v⟫_ℝ) t :=
    fun t ht => (line_hasDeriv (hd _ (hmem t ht)) xb v t rfl).sub_const (f xb)
  have hnear : ∀ t ∈ Set.Ioc (0 : ℝ) 1, IsNearest (optSet X f) (xb + t • v) xb :=
    fun t ht => nearest_seg hb ⟨ht.1.le, ht.2⟩
  have hkey : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      φ t + κ / 2 * (t * r) ^ 2 ≤ t * ⟪gradient f (xb + t • v), v⟫_ℝ := by
    intro t ht
    have hI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h := hqs _ (hmem t hI) xb (hnear t ht)
    have e1 : xb + t • v - xb = t • v := by abel
    have n1 : ‖xb + t • v - xb‖ = t * r := by
      rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have e3 : xb - (xb + t • v) = -(t • v) := by abel
    rw [e3, inner_neg_right, real_inner_smul_right, n1] at h
    simp only [φ]
    linarith
  let h : ℝ → ℝ := fun t => φ t / t - κ * r ^ 2 / 2 * t
  have hh : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt h
      ((⟪gradient f (xb + t • v), v⟫_ℝ * t - φ t) / t ^ 2 - κ * r ^ 2 / 2) t := by
    intro t ht
    have hI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have h1 := (hφ t hI).div (hasDerivAt_id t) ht.1.ne'
    have h2 := (hasDerivAt_id t).const_mul (κ * r ^ 2 / 2)
    refine (h1.sub h2).congr_deriv ?_
    simp
  have hmono : MonotoneOn h (Set.Ioc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
    · intro t ht; exact (hh t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact (hh t (Set.Ioo_subset_Ioc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      have ht' := Set.Ioo_subset_Ioc_self ht
      rw [(hh t ht').deriv]
      have := hkey t ht'
      have hp : 0 < t ^ 2 := pow_pos ht.1 2
      have : κ * r ^ 2 / 2 ≤ (⟪gradient f (xb + t • v), v⟫_ℝ * t - φ t) / t ^ 2 := by
        rw [le_div_iff₀ hp]; nlinarith
      linarith
  have hlim : Tendsto h (𝓝[>] 0) (𝓝 ⟪gradient f xb, v⟫_ℝ) := by
    have h1 := slope_tendsto (hd xb hxb) v
    have h2 : Tendsto (fun ε : ℝ => κ * r ^ 2 / 2 * ε) (𝓝[>] 0) (𝓝 (κ * r ^ 2 / 2 * 0)) :=
      ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    have h3 := h1.sub h2
    rw [mul_zero, sub_zero] at h3
    exact h3
  have hle : ⟪gradient f xb, v⟫_ℝ ≤ h 1 := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact hmono ⟨hε.1, hε.2.le⟩ ⟨one_pos, le_rfl⟩ hε.2.le
  have e : xb + (1 : ℝ) • v = x := by simp [hv]
  simp only [h, φ, e, div_one, mul_one] at hle
  linarith

theorem gg_under {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {κ : ℝ} (hg : QuadGradGrowth X f κ) :
    QuadUnder X f κ := by
  intro x hx xb hb
  have hxb : xb ∈ X := hb.1.1
  set v := x - xb with hv
  set r := ‖v‖ with hr
  set I0 := ⟪gradient f xb, v⟫_ℝ with hI0
  let g : ℝ → ℝ := fun t => f (xb + t • v) - f xb - t * I0 - κ / 2 * t ^ 2 * r ^ 2
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, xb + t • v ∈ X := fun t ht => line_mem hX hxb hx ht
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g
      (⟪gradient f (xb + t • v), v⟫_ℝ - I0 - κ * t * r ^ 2) t := by
    intro t ht
    have h1 := (line_hasDeriv (hd _ (hmem t ht)) xb v t rfl).sub_const (f xb)
    have h2 : HasDerivAt (fun s : ℝ => s * I0) I0 t := by
      simpa using (hasDerivAt_id t).mul_const I0
    have h3 : HasDerivAt (fun s : ℝ => κ / 2 * s ^ 2 * r ^ 2) (κ * t * r ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (κ / 2)).mul_const (r ^ 2)
      refine this.congr_deriv ?_
      first | ring | (norm_num; ring) | norm_num
    exact (h1.sub h2).sub h3
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      rw [(hder t ht').deriv]
      have h := hg _ (hmem t ht') xb (nearest_seg hb ht')
      have e1 : xb + t • v - xb = t • v := by abel
      have n1 : ‖t • v‖ = t * r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [e1, n1, real_inner_smul_right, inner_sub_left] at h
      have h' : t * (κ * t * r ^ 2) ≤ t * (⟪gradient f (xb + t • v), v⟫_ℝ - I0) := by
        nlinarith
      have := le_of_mul_le_mul_left h' ht.1
      linarith
  have h01 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have e : xb + (1 : ℝ) • v = x := by simp [hv]
  have h0 : g 0 = 0 := by simp [g]
  have h1 : g 1 = f x - f xb - I0 - κ / 2 * r ^ 2 := by
    show f (xb + (1 : ℝ) • v) - f xb - 1 * I0 - κ / 2 * 1 ^ 2 * r ^ 2 = _
    rw [e]; ring
  rw [h0, h1] at h01
  linarith

theorem qu_fg {X : Set (E n)} (hX : Convex ℝ X) {f : E n → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {κ : ℝ} (hq : QuadUnder X f κ) :
    QuadFunGrowth X f κ := by
  intro x hx xb hb
  have h := hq x hx xb hb
  have hI : 0 ≤ ⟪gradient f xb, x - xb⟫_ℝ := by
    have h1 := slope_tendsto (hd xb hb.1.1) (x - xb)
    apply ge_of_tendsto h1
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
    have := hb.1.2 _ (line_mem hX hb.1.1 hx ⟨hε.1.le, hε.2⟩)
    exact div_nonneg (by linarith) hε.1.le
  linarith

end NGP
end NGSec

theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (xstar : NecoaraNG.Chain.E n)
    (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f) :
    ∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (xbar + t • (x - xbar)) xbar := by
  intro x _ xbar hb t ht
  exact NGP.nearest_seg hb ht
