-- Prove2me | solution 1 for GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:57.897776+00:00
-- url     : https://prove2.me/submissions/78809a7a-2c8b-4849-8ac6-93b602e632b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentCoeffNegEqZeroOfBounded
import Theorems.Thm_GlobalTheory_norm_eTwoPi_I_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : ℂ⸨X⸩) (T C : ℝ),
    (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) →
    ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  intro F T C h m hm
  by_contra hne
  have hF : F ≠ 0 := by rintro rfl; exact hne (by simp)
  have hm₀le : F.order ≤ m := by
    by_contra hlt; push_neg at hlt; exact hne (HahnSeries.coeff_eq_zero_of_lt_order hlt)
  have hc : F.coeff F.order ≠ 0 := fun h0 => hF (HahnSeries.coeff_order_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (le_of_lt (lt_of_le_of_lt hm₀le hm))
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  set m₀ := F.order with hm₀
  set y₁ : ℝ := max T 0 + 1 with hy₁
  have hy₁T : T < y₁ := by have := le_max_left T 0; linarith
  have hy₁0 : 0 < y₁ := by have := le_max_right T 0; linarith
  obtain ⟨x₁, hx₁, -⟩ := h (Complex.I * y₁) (by simpa using hy₁T)
  set q₁ := eTwoPi (Complex.I * y₁) with hq₁
  set ρ₁ := ‖q₁‖ with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁, hq₁, norm_eTwoPi_I_mul]; exact Real.exp_pos _
  have hS : Summable (fun m : ℤ => ‖F.coeff m * q₁ ^ m‖) := hx₁.summable.norm
  set S := ∑' m : ℤ, ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k with hSdef
  have key : ∀ y : ℝ, y₁ ≤ y →
      ‖F.coeff m₀‖ ≤ C * Real.exp (-(2 * Real.pi * y)) ^ k + Real.exp (-(2 * Real.pi * y)) / ρ₁ * S := by
    intro y hy
    obtain ⟨x, hx, hxC⟩ := h (Complex.I * y) (by simpa using lt_of_lt_of_le hy₁T hy)
    set q := eTwoPi (Complex.I * y) with hq
    set ρ := ‖q‖ with hρ
    have hρe : ρ = Real.exp (-(2 * Real.pi * y)) := norm_eTwoPi_I_mul y
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρe, hρ₁, hq₁, norm_eTwoPi_I_mul, Real.exp_le_exp]
      nlinarith [Real.pi_pos]
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    set r : ℤ → ℂ := fun m => F.coeff m * q ^ m * q ^ k - (if m = m₀ then F.coeff m₀ else 0) with hr
    have h2 : HasSum r (x * q ^ k - F.coeff m₀) := (hx.mul_right (q ^ k)).sub (hasSum_ite_eq m₀ _)
    have hbd : ∀ m, ‖r m‖ ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by
      intro m
      have hRnn : 0 ≤ ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k) := by positivity
      by_cases hmm : m = m₀
      · subst hmm
        have : q ^ m₀ * q ^ k = 1 := by
          rw [hk, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq0)]
        have : r m₀ = 0 := by simp only [hr, mul_assoc, this, mul_one]; simp
        rw [this, norm_zero]; exact hRnn
      rcases lt_or_gt_of_ne hmm with hlt | hgt
      · have : r m = 0 := by simp only [hr, if_neg hmm, HahnSeries.coeff_eq_zero_of_lt_order hlt, zero_mul, sub_zero]
        rw [this, norm_zero]; exact hRnn
      · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0:ℤ) ≤ m - m₀ - 1 by omega)
        have hm : m = (n + 1 : ℕ) - (k : ℤ) := by push_cast; omega
        have e1 : ∀ t : ℝ, t ≠ 0 → t ^ m * t ^ k = t ^ (n + 1) := fun t ht => by
          rw [← zpow_natCast t k, ← zpow_add₀ ht, ← zpow_natCast]; congr 1; omega
        have hρpos : 0 < ρ := by rw [hρe]; exact Real.exp_pos _
        have hrm : ‖r m‖ = ‖F.coeff m‖ * (ρ ^ m * ρ ^ k) := by
          simp only [hr, if_neg hmm, sub_zero, norm_mul, norm_pow, norm_zpow, ← hρ, mul_assoc]
        have hq₁m : ‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k = ‖F.coeff m‖ * (ρ₁ ^ m * ρ₁ ^ k) := by
          rw [norm_mul, norm_zpow, ← hρ₁, mul_assoc]
        rw [hrm, hq₁m, e1 ρ hρpos.ne', e1 ρ₁ hρ₁pos.ne']
        have hpow : ρ ^ n ≤ ρ₁ ^ n := pow_le_pow_left₀ hρ0 hρle n
        have hc0 : 0 ≤ ‖F.coeff m‖ := norm_nonneg _
        rw [pow_succ, pow_succ]
        calc ‖F.coeff m‖ * (ρ ^ n * ρ) ≤ ‖F.coeff m‖ * (ρ₁ ^ n * ρ) := by gcongr
          _ = ρ / ρ₁ * (‖F.coeff m‖ * (ρ₁ ^ n * ρ₁)) := by field_simp
    have hg : HasSum (fun m => ρ / ρ₁ * (‖F.coeff m * q₁ ^ m‖ * ρ₁ ^ k)) (ρ / ρ₁ * S) :=
      (hS.mul_right (ρ₁ ^ k)).hasSum.mul_left _
    have h3 : ‖x * q ^ k - F.coeff m₀‖ ≤ ρ / ρ₁ * S := by
      rw [← h2.tsum_eq]; exact tsum_of_norm_bounded hg hbd
    have h4 : ‖x * q ^ k‖ ≤ C * ρ ^ k := by
      rw [norm_mul, norm_pow]; exact mul_le_mul_of_nonneg_right hxC (by positivity)
    rw [← hρe]
    calc ‖F.coeff m₀‖ = ‖x * q ^ k - (x * q ^ k - F.coeff m₀)‖ := by ring_nf
      _ ≤ ‖x * q ^ k‖ + ‖x * q ^ k - F.coeff m₀‖ := norm_sub_le _ _
      _ ≤ C * ρ ^ k + ρ / ρ₁ * S := add_le_add h4 h3
  have hlim : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
      (Filter.tendsto_id.const_mul_atTop (by positivity)))
  have hlim2 : Filter.Tendsto (fun y : ℝ => C * Real.exp (-(2 * Real.pi * y)) ^ k +
      Real.exp (-(2 * Real.pi * y)) / ρ₁ * S) Filter.atTop (nhds 0) := by
    have := ((hlim.pow k).const_mul C).add ((hlim.div_const ρ₁).mul_const S)
    simpa [zero_pow hk0] using this
  have hle : ‖F.coeff m₀‖ ≤ 0 :=
    ge_of_tendsto hlim2 (Filter.eventually_atTop.2 ⟨y₁, key⟩)
  exact hc (norm_le_zero_iff.1 hle)
end GlobalTheory
