-- Prove2me | solution 1 for LiuVanRyzin.focLHS_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:27:25.061072+00:00
-- url     : https://prove2.me/submissions/ac489a3d-acb9-42e1-b8f7-a5641cdfb2fc

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

set_option autoImplicit false

namespace LVR2f297eb1

/-- `h(t) = t^γ (γ + (1-γ) t) / t` is strictly decreasing on `(0,1)` (weighted AM-GM). -/
theorem h_anti (γ s t : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hs : 0 < s) (hst : s < t)
    (ht : t < 1) :
    t ^ γ * (γ + (1 - γ) * t) / t < s ^ γ * (γ + (1 - γ) * s) / s := by
  have ht0 : 0 < t := lt_trans hs hst
  have hg : 0 < 1 - γ := by linarith
  have hr0 : 0 < s / t := div_pos hs ht0
  have hr1 : s / t < 1 := by rw [div_lt_one ht0]; exact hst
  have hsr : s = (s / t) * t := by field_simp
  have hpow : s ^ γ = (s / t) ^ γ * t ^ γ := by
    conv_lhs => rw [hsr]
    rw [Real.mul_rpow hr0.le ht0.le]
  have hA : (s / t) ^ γ * (s / t) ^ (1 - γ) = s / t := by
    rw [← Real.rpow_add hr0]; simp
  have hAM : (s / t) ^ (1 - γ) ≤ (1 - γ) * (s / t) + γ := by
    have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - γ) (w₂ := γ) (p₁ := s / t)
      (p₂ := 1) hg.le hγ0.le hr0.le zero_le_one (by ring)
    simpa using this
  have hpos1 : 0 < γ + (1 - γ) * t := by nlinarith
  have key : (s / t) ^ (1 - γ) * (γ + (1 - γ) * t) < γ + (1 - γ) * s := by
    calc (s / t) ^ (1 - γ) * (γ + (1 - γ) * t)
        ≤ ((1 - γ) * (s / t) + γ) * (γ + (1 - γ) * t) :=
          mul_le_mul_of_nonneg_right hAM hpos1.le
      _ < γ + (1 - γ) * s := by
          have hprod : 0 < γ * (1 - γ) * ((1 - s / t) * (1 - t)) :=
            mul_pos (mul_pos hγ0 hg) (mul_pos (by linarith) (by linarith))
          have e2 : (1 - γ) * s = (1 - γ) * ((s / t) * t) := by rw [← hsr]
          nlinarith [hprod, e2]
  have hP : 0 < t ^ γ := Real.rpow_pos_of_pos ht0 γ
  have hR : 0 < (s / t) ^ γ := Real.rpow_pos_of_pos hr0 γ
  have hs' : s = (s / t) ^ γ * (s / t) ^ (1 - γ) * t := by rw [hA]; exact hsr
  rw [div_lt_div_iff₀ ht0 hs, hpow]
  calc t ^ γ * (γ + (1 - γ) * t) * s
      = (t ^ γ * t * (s / t) ^ γ) * ((s / t) ^ (1 - γ) * (γ + (1 - γ) * t)) := by
        conv_lhs => rw [hs']
        ring
    _ < (t ^ γ * t * (s / t) ^ γ) * (γ + (1 - γ) * s) :=
        mul_lt_mul_of_pos_left key (by positivity)
    _ = (s / t) ^ γ * t ^ γ * (γ + (1 - γ) * s) * t := by ring

open LiuVanRyzin in
theorem form (p₁ p₂ α γ v : ℝ) (hp : p₂ < p₁) (hv : p₁ < v) :
    focLHS p₁ p₂ α γ v =
      ((v - p₁) / (v - p₂)) ^ γ * (γ + (1 - γ) * ((v - p₁) / (v - p₂))) /
        ((v - p₁) / (v - p₂)) - (p₁ - α) / (p₂ - α) := by
  have hu : 0 < v - p₁ := by linarith
  have hw : 0 < v - p₂ := by linarith
  have hT : 0 < (v - p₁) / (v - p₂) := div_pos hu hw
  have e : 1 + γ * (p₁ - p₂) / (v - p₁) =
      (γ + (1 - γ) * ((v - p₁) / (v - p₂))) / ((v - p₁) / (v - p₂)) := by
    rw [eq_div_iff hT.ne']
    field_simp
    ring
  unfold focLHS fillRate
  rw [e]
  ring

theorem T_mono (p₁ p₂ a b : ℝ) (hp : p₂ < p₁) (ha : p₁ < a) (hab : a < b) :
    (a - p₁) / (a - p₂) < (b - p₁) / (b - p₂) := by
  have h1 : 0 < a - p₂ := by linarith
  have h2 : 0 < b - p₂ := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

theorem T_pos (p₁ p₂ a : ℝ) (hp : p₂ < p₁) (ha : p₁ < a) : 0 < (a - p₁) / (a - p₂) :=
  div_pos (by linarith) (by linarith)

theorem T_lt_one (p₁ p₂ a : ℝ) (hp : p₂ < p₁) (ha : p₁ < a) : (a - p₁) / (a - p₂) < 1 := by
  rw [div_lt_one (by linarith)]; linarith

open LiuVanRyzin in
theorem anti (p₁ p₂ α γ : ℝ) (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (focLHS p₁ p₂ α γ) (Set.Ioi p₁) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  rw [form p₁ p₂ α γ a hp ha, form p₁ p₂ α γ b hp hb]
  apply sub_lt_sub_right
  exact h_anti γ _ _ hγ0 hγ1 (T_pos p₁ p₂ a hp ha) (T_mono p₁ p₂ a b hp ha hab)
    (T_lt_one p₁ p₂ b hp hb)

open LiuVanRyzin in
theorem pos_point (p₁ p₂ α γ : ℝ) (hα : α < p₂) (hp : p₂ < p₁)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : ∃ v₁, p₁ < v₁ ∧ 0 < focLHS p₁ p₂ α γ v₁ := by
  set K := (p₁ - α) / (p₂ - α) with hK
  have hb : 0 < p₂ - α := by linarith
  have hK1 : 1 < K := by rw [hK, one_lt_div hb]; linarith
  have hg : 0 < 1 - γ := by linarith
  have hx0 : 0 < γ / (2 * K) := by positivity
  have hx1 : γ / (2 * K) < 1 := by rw [div_lt_one (by linarith)]; linarith
  set t := (γ / (2 * K)) ^ (1 - γ)⁻¹ with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have ht1 : t < 1 := Real.rpow_lt_one hx0.le hx1 (inv_pos.mpr hg)
  have htp : t ^ (1 - γ) = γ / (2 * K) := Real.rpow_inv_rpow hx0.le hg.ne'
  have hd : 0 < p₁ - p₂ := by linarith
  have hu : 0 < t * (p₁ - p₂) / (1 - t) := div_pos (mul_pos ht0 hd) (by linarith)
  refine ⟨p₁ + t * (p₁ - p₂) / (1 - t), by linarith, ?_⟩
  rw [form p₁ p₂ α γ _ hp (by linarith)]
  have hT : (p₁ + t * (p₁ - p₂) / (1 - t) - p₁) / (p₁ + t * (p₁ - p₂) / (1 - t) - p₂) = t := by
    have h1t : (1 - t) ≠ 0 := by linarith
    have hX : t * (p₁ - p₂) / (1 - t) * (1 - t) = t * (p₁ - p₂) := div_mul_cancel₀ _ h1t
    rw [div_eq_iff (by linarith)]
    linear_combination hX
  rw [hT, sub_pos]
  have hsplit : t ^ γ * t ^ (1 - γ) = t := by rw [← Real.rpow_add ht0]; simp
  have hPg : 0 < t ^ γ := Real.rpow_pos_of_pos ht0 γ
  -- t^γ * (γ + (1-γ) t) / t ≥ γ t^γ / t = γ / t^(1-γ) = 2K
  rw [lt_div_iff₀ ht0]
  have hK0 : 0 < K := by linarith
  have : t ^ γ * γ = 2 * K * t := by
    calc t ^ γ * γ = t ^ γ * (2 * K * t ^ (1 - γ)) := by
          rw [htp]; field_simp
      _ = 2 * K * (t ^ γ * t ^ (1 - γ)) := by ring
      _ = 2 * K * t := by rw [hsplit]
  nlinarith [mul_pos hPg (mul_pos hg ht0)]

open LiuVanRyzin in
theorem neg_far (p₁ p₂ α γ v : ℝ) (hα : α < p₂) (hp : p₂ < p₁)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hv : p₁ + γ * (p₂ - α) < v) :
    focLHS p₁ p₂ α γ v < 0 := by
  have hb : 0 < p₂ - α := by linarith
  have hd : 0 < p₁ - p₂ := by linarith
  have hgd : 0 < γ * (p₁ - p₂) := mul_pos hγ0 hd
  have hgb : 0 < γ * (p₂ - α) := mul_pos hγ0 hb
  have ht : 0 < v - p₁ := by linarith
  have hs : 0 < v - p₂ := by linarith
  have hx0 : 0 ≤ (v - p₁) / (v - p₂) := div_nonneg ht.le hs.le
  have hx1 : (v - p₁) / (v - p₂) < 1 := by
    rw [div_lt_one hs]; linarith
  have hq : fillRate p₁ p₂ γ v < 1 := Real.rpow_lt_one hx0 hx1 hγ0
  have hF : 0 < 1 + γ * (p₁ - p₂) / (v - p₁) := by
    have := div_pos hgd ht
    linarith
  have hF2 : 1 + γ * (p₁ - p₂) / (v - p₁) ≤ (p₁ - α) / (p₂ - α) := by
    rw [add_div' _ _ _ ht.ne', div_le_div_iff₀ ht hb]
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hv.le)]
  unfold focLHS
  have hm := mul_lt_mul_of_pos_right hq hF
  rw [one_mul] at hm
  linarith

open LiuVanRyzin in
theorem cont (p₁ p₂ α γ a b : ℝ) (hp : p₂ < p₁) (ha : p₁ < a) (hγ0 : 0 < γ) :
    ContinuousOn (focLHS p₁ p₂ α γ) (Set.Icc a b) := by
  unfold focLHS fillRate
  have hc : Continuous (fun x : ℝ => x ^ γ) := Real.continuous_rpow_const hγ0.le
  apply ContinuousOn.sub _ continuousOn_const
  apply ContinuousOn.mul
  · apply hc.comp_continuousOn
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; have := hx.1; linarith
  · apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; have := hx.1; linarith

end LVR2f297eb1

open LiuVanRyzin Filter Topology in
theorem solution (p₁ p₂ α γ : ℝ) (hα : α < p₂) (hp : p₂ < p₁)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (focLHS p₁ p₂ α γ) (Set.Ioi p₁) ∧
      (∀ᶠ v in 𝓝[>] p₁, 0 < focLHS p₁ p₂ α γ v) ∧
      (∀ᶠ v in atTop, focLHS p₁ p₂ α γ v < 0) ∧
      ∃! v₀ : ℝ, p₁ < v₀ ∧ focLHS p₁ p₂ α γ v₀ = 0 := by
  have hA := LVR2f297eb1.anti p₁ p₂ α γ hp hγ0 hγ1
  obtain ⟨v₁, hv₁, hf₁⟩ := LVR2f297eb1.pos_point p₁ p₂ α γ hα hp hγ0 hγ1
  have hb : 0 < p₂ - α := by linarith
  have hgb : 0 < γ * (p₂ - α) := mul_pos hγ0 hb
  refine ⟨hA, ?_, ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hv₁] with v hv
    exact lt_trans hf₁ (hA hv.1 hv₁ hv.2)
  · filter_upwards [eventually_gt_atTop (p₁ + γ * (p₂ - α))] with v hv
    exact LVR2f297eb1.neg_far p₁ p₂ α γ v hα hp hγ0 hγ1 hv
  · set v₂ := max v₁ (p₁ + γ * (p₂ - α)) + 1 with hv₂
    have h12 : v₁ ≤ v₂ := by
      have := le_max_left v₁ (p₁ + γ * (p₂ - α)); linarith
    have hf₂ : focLHS p₁ p₂ α γ v₂ < 0 := by
      apply LVR2f297eb1.neg_far p₁ p₂ α γ v₂ hα hp hγ0 hγ1
      have := le_max_right v₁ (p₁ + γ * (p₂ - α)); linarith
    have hivt := intermediate_value_Icc' h12 (LVR2f297eb1.cont p₁ p₂ α γ v₁ v₂ hp hv₁ hγ0)
    obtain ⟨c, hc, hc0⟩ := hivt ⟨hf₂.le, hf₁.le⟩
    refine ⟨c, ⟨lt_of_lt_of_le hv₁ hc.1, hc0⟩, ?_⟩
    rintro y ⟨hy, hy0⟩
    exact hA.injOn hy (lt_of_lt_of_le hv₁ hc.1) (hy0.trans hc0.symm)

#print axioms solution
