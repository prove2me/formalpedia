-- Prove2me | solution 1 for LiuVanRyzin.optimal_stocking
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T04:12:05.671989+00:00
-- url     : https://prove2.me/submissions/cc4c41e0-b39a-4700-afe0-e11c59bf087b

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

set_option autoImplicit false


/- Inlined checked module: PowerTangent -/
section
namespace LiuVanRyzin.Proof

theorem weighted_product_tangent {gamma x y a b : ℝ}
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 < a) (hb : 0 < b) :
    x ^ gamma * y ^ (1 - gamma) ≤
      a ^ gamma * b ^ (1 - gamma) * (gamma * (x / a) + (1 - gamma) * (y / b)) := by
  have hA := Real.geom_mean_le_arith_mean2_weighted hg0 (sub_nonneg.mpr hg1)
    (div_nonneg hx ha.le) (div_nonneg hy hb.le) (by ring : gamma + (1 - gamma) = 1)
  have hap : 0 < a ^ gamma := Real.rpow_pos_of_pos ha _
  have hbp : 0 < b ^ (1 - gamma) := Real.rpow_pos_of_pos hb _
  calc
    x ^ gamma * y ^ (1 - gamma) =
        (a ^ gamma * b ^ (1 - gamma)) * ((x / a) ^ gamma * (y / b) ^ (1 - gamma)) := by
      rw [Real.div_rpow hx ha.le, Real.div_rpow hy hb.le]
      field_simp [ne_of_gt hap, ne_of_gt hbp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (mul_pos hap hbp).le

theorem power_ratio_factorization {t d gamma : ℝ} (ht : 0 ≤ t) (htd : 0 < t + d) :
    (t + d) * (t / (t + d)) ^ gamma = t ^ gamma * (t + d) ^ (1 - gamma) := by
  rw [Real.div_rpow ht htd.le, Real.rpow_sub htd, Real.rpow_one]
  ring

theorem power_tangent {t s d gamma : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (hd : 0 < d)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    t ^ gamma * (t + d) ^ (1 - gamma) ≤
      s ^ gamma * (s + d) ^ (1 - gamma) +
        (s / (s + d)) ^ gamma * (1 + gamma * d / s) * (t - s) := by
  have hsD : 0 < s + d := add_pos hs hd
  have h := weighted_product_tangent hg0 hg1 ht (add_nonneg ht hd.le) hs hsD
  calc
    _ ≤ s ^ gamma * (s + d) ^ (1 - gamma) *
        (gamma * (t / s) + (1 - gamma) * ((t + d) / (s + d))) := h
    _ = _ := by
      rw [← power_ratio_factorization hs.le hsD]
      field_simp [ne_of_gt hs, ne_of_gt hsD]
      ring

end LiuVanRyzin.Proof
end


/- Inlined checked module: ProfitTangent -/
section
namespace LiuVanRyzin.Proof

theorem fillRate_factorization {p1 p2 gamma v : ℝ} (hp : p2 < p1) (hv : p1 ≤ v) :
    (v - p2) * fillRate p1 p2 gamma v =
      (v - p1) ^ gamma * (v - p2) ^ (1 - gamma) := by
  unfold fillRate
  rw [Real.div_rpow (sub_nonneg.mpr hv) (by linarith : 0 ≤ v - p2),
    Real.rpow_sub (by linarith : 0 < v - p2), Real.rpow_one]
  ring

theorem fillRate_component_tangent {p1 p2 gamma v v0 : ℝ} (hp : p2 < p1)
    (hv : p1 ≤ v) (hv0 : p1 < v0) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    (v - p2) * fillRate p1 p2 gamma v ≤
      (v0 - p2) * fillRate p1 p2 gamma v0 +
        (fillRate p1 p2 gamma v0 * (1 + gamma * (p1 - p2) / (v0 - p1))) * (v - v0) := by
  have h := power_tangent (t := v - p1) (s := v0 - p1) (d := p1 - p2)
    (sub_nonneg.mpr hv) (sub_pos.mpr hv0) (sub_pos.mpr hp) hg0 hg1
  rw [fillRate_factorization hp hv, fillRate_factorization hp hv0.le]
  simpa only [sub_add_sub_cancel, sub_sub_sub_cancel_right, fillRate] using h

theorem segProfit_global_max (N Ubar p1 p2 alpha gamma v0 : ℝ)
    (hN : 0 < N) (hU : 0 < Ubar) (ha : alpha < p2) (hp : p2 < p1)
    (hg0 : 0 < gamma) (hg1 : gamma < 1) (hv0 : p1 < v0)
    (hroot : focLHS p1 p2 alpha gamma v0 = 0) :
    ∀ v : ℝ, p1 ≤ v → segProfit N Ubar p1 p2 alpha gamma v ≤
      segProfit N Ubar p1 p2 alpha gamma v0 := by
  intro v hv
  have hb : 0 < p2 - alpha := sub_pos.mpr ha
  have hcoef : (p2 - alpha) *
      (fillRate p1 p2 gamma v0 * (1 + gamma * (p1 - p2) / (v0 - p1))) = p1 - alpha := by
    unfold focLHS at hroot
    have he := (sub_eq_zero.mp hroot)
    have hm := (eq_div_iff (ne_of_gt hb)).mp he
    simpa only [mul_comm] using hm
  have ht := fillRate_component_tangent hp hv hv0 hg0.le hg1.le
  have hprod : (p2 - alpha) * ((v - p2) * fillRate p1 p2 gamma v) ≤
      (p2 - alpha) * ((v0 - p2) * fillRate p1 p2 gamma v0) + (p1 - alpha) * (v - v0) := by
    calc
      _ ≤ (p2 - alpha) * ((v0 - p2) * fillRate p1 p2 gamma v0 +
          (fillRate p1 p2 gamma v0 * (1 + gamma * (p1 - p2) / (v0 - p1))) * (v - v0)) :=
        mul_le_mul_of_nonneg_left ht hb.le
      _ = _ := by
        rw [mul_add, ← mul_assoc (p2 - alpha)
          (fillRate p1 p2 gamma v0 * (1 + gamma * (p1 - p2) / (v0 - p1))) (v - v0), hcoef]
  unfold segProfit
  apply mul_le_mul_of_nonneg_left _ (div_pos hN hU).le
  nlinarith only [hprod]

end LiuVanRyzin.Proof
end


/- Inlined checked module: CriticalThreshold -/
section
namespace LiuVanRyzin.Proof

theorem fillRate_bounds {p₁ p₂ γ v : ℝ} (hp : p₂ < p₁) (hγ : 0 < γ)
    (hv : p₁ < v) : 0 < fillRate p₁ p₂ γ v ∧ fillRate p₁ p₂ γ v < 1 := by
  have hv₂ : 0 < v - p₂ := by linarith
  have hratio : 0 < (v - p₁) / (v - p₂) := div_pos (sub_pos.mpr hv) hv₂
  exact ⟨Real.rpow_pos_of_pos hratio γ,
    Real.rpow_lt_one hratio.le ((div_lt_one hv₂).mpr (by linarith)) hγ⟩

theorem foc_product {p₁ p₂ α γ v₀ : ℝ} (hα : α < p₂) (hv₀ : p₁ < v₀)
    (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    (p₂ - α) * fillRate p₁ p₂ γ v₀ * (v₀ - p₁ + γ * (p₁ - p₂)) =
      (p₁ - α) * (v₀ - p₁) := by
  have hh : fillRate p₁ p₂ γ v₀ * (1 + γ * (p₁ - p₂) / (v₀ - p₁)) =
      (p₁ - α) / (p₂ - α) := sub_eq_zero.mp hroot
  field_simp [(sub_pos.mpr hv₀).ne', (sub_pos.mpr hα).ne'] at hh
  nlinarith [hh]

theorem foc_fillRate {p₁ p₂ α γ v₀ : ℝ} (hα : α < p₂) (hp : p₂ < p₁)
    (hγ : 0 < γ) (hv₀ : p₁ < v₀) (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    fillRate p₁ p₂ γ v₀ = ((p₁ - α) * (v₀ - p₁)) /
      ((p₂ - α) * (v₀ - p₁ + γ * (p₁ - p₂))) := by
  have hden : 0 < v₀ - p₁ + γ * (p₁ - p₂) :=
    add_pos (sub_pos.mpr hv₀) (mul_pos hγ (sub_pos.mpr hp))
  apply (eq_div_iff (mul_pos (sub_pos.mpr hα) hden).ne').mpr
  nlinarith [foc_product hα hv₀ hroot]

theorem root_offset_lt {p₁ p₂ α γ v₀ : ℝ} (hα : α < p₂) (hp : p₂ < p₁)
    (hγ : 0 < γ) (hv₀ : p₁ < v₀) (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    v₀ - p₁ < γ * (p₂ - α) := by
  have hd : 0 < p₁ - p₂ := sub_pos.mpr hp
  have hb : 0 < p₂ - α := sub_pos.mpr hα
  have hden : 0 < v₀ - p₁ + γ * (p₁ - p₂) :=
    add_pos (sub_pos.mpr hv₀) (mul_pos hγ hd)
  have hlt := mul_lt_mul_of_pos_right (fillRate_bounds hp hγ hv₀).2 (mul_pos hb hden)
  have heq := foc_product hα hv₀ hroot
  nlinarith

theorem criticalU_sub_root {p₁ p₂ α γ v₀ : ℝ} (hp : p₂ < p₁)
    (hγ : 0 < γ) (hv₀ : p₁ < v₀) :
    criticalU p₁ p₂ α γ v₀ - v₀ =
      (v₀ - p₂) * (γ * (p₂ - α) - (v₀ - p₁)) /
        (v₀ - p₁ + γ * (p₁ - p₂)) := by
  have hden : 0 < v₀ - p₁ + γ * (p₁ - p₂) :=
    add_pos (sub_pos.mpr hv₀) (mul_pos hγ (sub_pos.mpr hp))
  unfold criticalU
  field_simp [hden.ne']
  ring

theorem root_lt_criticalU {p₁ p₂ α γ v₀ : ℝ} (hα : α < p₂) (hp : p₂ < p₁)
    (hγ : 0 < γ) (hv₀ : p₁ < v₀) (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    v₀ < criticalU p₁ p₂ α γ v₀ := by
  apply sub_pos.mp
  rw [criticalU_sub_root hp hγ hv₀]
  exact div_pos (mul_pos (by linarith) (sub_pos.mpr (root_offset_lt hα hp hγ hv₀ hroot)))
    (add_pos (sub_pos.mpr hv₀) (mul_pos hγ (sub_pos.mpr hp)))

theorem profit_difference (N Ubar : ℝ) {p₁ p₂ α γ v₀ : ℝ}
    (hα : α < p₂) (hp : p₂ < p₁) (hγ : 0 < γ) (hv₀ : p₁ < v₀)
    (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    segProfit N Ubar p₁ p₂ α γ v₀ - lowPriceProfit N Ubar p₂ α =
      (N / Ubar) * (p₁ - p₂) * (Ubar - criticalU p₁ p₂ α γ v₀) := by
  have hden : 0 < v₀ - p₁ + γ * (p₁ - p₂) :=
    add_pos (sub_pos.mpr hv₀) (mul_pos hγ (sub_pos.mpr hp))
  rw [segProfit, lowPriceProfit, foc_fillRate hα hp hγ hv₀ hroot]
  suffices (p₁ - α) * (Ubar - v₀) +
      (p₂ - α) * (v₀ - p₂) *
        (((p₁ - α) * (v₀ - p₁)) / ((p₂ - α) * (v₀ - p₁ + γ * (p₁ - p₂)))) -
      (p₂ - α) * (Ubar - p₂) = (p₁ - p₂) * (Ubar - criticalU p₁ p₂ α γ v₀) by
    nlinarith [congrArg (fun x : ℝ => (N / Ubar) * x) this]
  unfold criticalU
  field_simp [hden.ne', (sub_pos.mpr hα).ne']
  ring

end LiuVanRyzin.Proof
end


/- Inlined checked module: RationingRoot -/
section
namespace LiuVanRyzin

/-- Proposition 3 (Liu–van Ryzin 2008, p. 1122). Let `v⁰` be the root of (7) and `U_c` as in
(8). If `Ū ≥ U_c`, segmentation at `v⁰` is optimal: `v⁰` maximizes `Π` on `[p₁, Ū]` and
`Π(v⁰) ≥ Π^NS`. Otherwise serving the entire market at the low price is optimal:
`Π(v) ≤ Π^NS` for every `v ∈ [p₁, Ū]`. -/
theorem optimal_stocking (N Ubar p₁ p₂ α γ v₀ : ℝ) (hN : 0 < N) (hα : α < p₂)
    (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp₂ : 0 ≤ p₂) (hpU : p₂ < Ubar)
    (hv₀ : p₁ < v₀) (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    (criticalU p₁ p₂ α γ v₀ ≤ Ubar →
        v₀ ∈ Set.Icc p₁ Ubar ∧
          IsMaxOn (segProfit N Ubar p₁ p₂ α γ) (Set.Icc p₁ Ubar) v₀ ∧
          lowPriceProfit N Ubar p₂ α ≤ segProfit N Ubar p₁ p₂ α γ v₀) ∧
      (Ubar < criticalU p₁ p₂ α γ v₀ →
        ∀ v ∈ Set.Icc p₁ Ubar, segProfit N Ubar p₁ p₂ α γ v ≤ lowPriceProfit N Ubar p₂ α) := by
  have hU : 0 < Ubar := lt_of_le_of_lt hp₂ hpU
  have hscale : 0 < (N / Ubar) * (p₁ - p₂) :=
    mul_pos (div_pos hN hU) (sub_pos.mpr hp)
  have hmax := Proof.segProfit_global_max N Ubar p₁ p₂ α γ v₀
    hN hU hα hp hγ0 hγ1 hv₀ hroot
  have hgap := Proof.profit_difference N Ubar hα hp hγ0 hv₀ hroot
  have hcrit := Proof.root_lt_criticalU hα hp hγ0 hv₀ hroot
  constructor
  · intro hc
    refine ⟨⟨hv₀.le, hcrit.le.trans hc⟩, ?_, ?_⟩
    · intro v hv
      exact hmax v hv.1
    · have hs := mul_nonneg hscale.le (sub_nonneg.mpr hc)
      linarith
  · intro hc v hv
    have hs := mul_nonpos_of_nonneg_of_nonpos hscale.le (sub_nonpos.mpr hc.le)
    have hbound : segProfit N Ubar p₁ p₂ α γ v₀ ≤ lowPriceProfit N Ubar p₂ α := by
      linarith
    exact (hmax v hv.1).trans hbound

end LiuVanRyzin
end


open LiuVanRyzin

theorem solution (N Ubar p₁ p₂ α γ v₀ : ℝ) (hN : 0 < N) (hα : α < p₂)
    (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp₂ : 0 ≤ p₂) (hpU : p₂ < Ubar)
    (hv₀ : p₁ < v₀) (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    (criticalU p₁ p₂ α γ v₀ ≤ Ubar →
        v₀ ∈ Set.Icc p₁ Ubar ∧
          IsMaxOn (segProfit N Ubar p₁ p₂ α γ) (Set.Icc p₁ Ubar) v₀ ∧
          lowPriceProfit N Ubar p₂ α ≤ segProfit N Ubar p₁ p₂ α γ v₀) ∧
      (Ubar < criticalU p₁ p₂ α γ v₀ →
        ∀ v ∈ Set.Icc p₁ Ubar, segProfit N Ubar p₁ p₂ α γ v ≤ lowPriceProfit N Ubar p₂ α) := LiuVanRyzin.optimal_stocking N Ubar p₁ p₂ α γ v₀ hN hα hp hγ0 hγ1 hp₂ hpU hv₀ hroot
