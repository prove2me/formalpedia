-- Prove2me | solution 1 for MeasureTheory.exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/48e518e3-baa2-5183-902b-8f8ddd75ee5e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

open FourierTransform

theorem solution
    {r : ℕ} (Ψ : (Fin r → ℝ) → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ Continuous Ψ ∧ Integrable Ψ ∧
      (∀ x : Fin r → ℝ, ‖Ψ x‖ ≤ C * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
      (∀ ξ : Fin r → ℝ,
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Ψ x‖ ≤
          C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) := by
  classical

  have hcont : Continuous Ψ := hΨ.continuous
  have hint : Integrable Ψ := hcont.integrable_of_hasCompactSupport hΨc
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hΨc
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)

  obtain ⟨R, hR⟩ := (hΨc.isCompact.isBounded).subset_closedBall 0
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hsupp : ∀ x : Fin r → ℝ, Ψ x ≠ 0 → ∀ k, |x k| ≤ R' := by
    intro x hx k
    have hxK : x ∈ tsupport Ψ := subset_tsupport _ hx
    have hxB := hR hxK
    rw [Metric.mem_closedBall, dist_zero_right] at hxB
    have := (norm_le_pi_norm x k).trans hxB
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

  have hprod : ∀ (ρ : ℝ), 0 ≤ ρ → ∀ y : Fin r → ℝ, (∀ k, |y k| ≤ ρ) →
      ((1 + ρ)⁻¹ ^ 2) ^ r ≤ ∏ k, (1 + |y k|)⁻¹ ^ 2 := by
    intro ρ hρ y hy
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => ?_)
    have h1 : (1 + ρ)⁻¹ ≤ (1 + |y k|)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]; linarith [hy k]
    exact pow_le_pow_left₀ (by positivity) h1 2

  set C₁ : ℝ := B * ((1 + R') ^ 2) ^ r with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hpt : ∀ x : Fin r → ℝ, ‖Ψ x‖ ≤ C₁ * ∏ k, (1 + |x k|)⁻¹ ^ 2 := by
    intro x
    by_cases hx : Ψ x = 0
    · rw [hx, norm_zero]; positivity
    · have hlow := hprod R' hR'0 x (hsupp x hx)
      have hkey : 1 ≤ ((1 + R') ^ 2) ^ r * ∏ k, (1 + |x k|)⁻¹ ^ 2 := by
        have : ((1 + R') ^ 2) ^ r * ((1 + R')⁻¹ ^ 2) ^ r = 1 := by
          rw [← mul_pow, ← mul_pow]; rw [mul_inv_cancel₀ (by positivity)]; simp
        calc (1 : ℝ) = ((1 + R') ^ 2) ^ r * ((1 + R')⁻¹ ^ 2) ^ r := this.symm
          _ ≤ ((1 + R') ^ 2) ^ r * ∏ k, (1 + |x k|)⁻¹ ^ 2 := mul_le_mul_of_nonneg_left hlow (by positivity)
      calc ‖Ψ x‖ ≤ B := hB x
        _ ≤ B * (((1 + R') ^ 2) ^ r * ∏ k, (1 + |x k|)⁻¹ ^ 2) := le_mul_of_one_le_right hB0 hkey
        _ = C₁ * ∏ k, (1 + |x k|)⁻¹ ^ 2 := by rw [hC₁]; ring

  let V := EuclideanSpace ℝ (Fin r)
  let Φ : V → ℂ := fun v => Ψ (WithLp.ofLp v)
  have hΦs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := hΨ.comp PiLp.contDiff_ofLp
  have hΦc : HasCompactSupport Φ := hΨc.comp_homeomorph (EuclideanSpace.equiv (Fin r) ℝ).toHomeomorph
  have hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ v : V, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n Φ v‖ ≤ C := by
    intro k n
    have hDc : HasCompactSupport (iteratedFDeriv ℝ n Φ) := hΦc.iteratedFDeriv n
    have hDcont : Continuous (iteratedFDeriv ℝ n Φ) :=
      hΦs.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨C₀, hC₀⟩ := hDcont.bounded_above_of_compact_support hDc
    obtain ⟨ρ, hρ⟩ := (hDc.isCompact.isBounded).subset_closedBall 0
    refine ⟨(max ρ 0) ^ k * max C₀ 0, fun v => ?_⟩
    by_cases hv : iteratedFDeriv ℝ n Φ v = 0
    · rw [hv, norm_zero, mul_zero]; positivity
    · have hvK := hρ (subset_tsupport _ hv)
      rw [Metric.mem_closedBall, dist_zero_right] at hvK
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hvK.trans (le_max_left _ _)) k)
        ((hC₀ v).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  let S : SchwartzMap V ℂ := SchwartzMap.mk Φ hΦs hdecay
  have hScoe : (S : V → ℂ) = Φ := rfl

  set FS : SchwartzMap V ℂ := SchwartzMap.fourierTransformCLM ℂ S with hFS
  have hFScoe : (FS : V → ℂ) = 𝓕 Φ := by
    rw [hFS, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, hScoe]
  set Ssup : ℝ := ((Finset.Iic ((2 * r, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) FS with hSsup
  have hSsup0 : 0 ≤ Ssup := apply_nonneg _ _
  have hFdec : ∀ w : V, (1 + ‖w‖) ^ (2 * r) * ‖(FS : V → ℂ) w‖ ≤ 2 ^ (2 * r) * Ssup := by
    intro w
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := ((2 * r, 0) : ℕ × ℕ)) (k := 2 * r) (n := 0)
      le_rfl le_rfl FS w
    rwa [norm_iteratedFDeriv_zero] at this

  have hFourier : ∀ ξ : Fin r → ℝ,
      ∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Ψ x
        = 𝓕 Φ (WithLp.toLp 2 ξ) := by
    intro ξ
    rw [Real.fourier_eq]
    rw [← (PiLp.volume_preserving_toLp (ι := Fin r)).integral_comp (MeasurableEquiv.toLp 2 (Fin r → ℝ)).measurableEmbedding]
    congr 1
    funext x
    rw [EuclideanSpace.inner_toLp_toLp, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    simp only [Φ, WithLp.ofLp_toLp, star_trivial, dotProduct]
    congr 1
    congr 1
    push_cast
    ring

  set C₂ : ℝ := 2 ^ (2 * r) * Ssup with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hft : ∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Ψ x‖ ≤
        C₂ * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by
    intro ξ
    rw [hFourier ξ, ← hFScoe]
    set w : V := WithLp.toLp 2 ξ with hw
    have hcoord : ∀ k, |ξ k| ≤ ‖w‖ := by
      intro k
      have := PiLp.norm_apply_le w k
      rw [hw, WithLp.ofLp_toLp, Real.norm_eq_abs] at this
      exact this
    have hlow := hprod ‖w‖ (norm_nonneg _) ξ hcoord
    have hpow : ((1 + ‖w‖)⁻¹ ^ 2) ^ r = ((1 + ‖w‖) ^ (2 * r))⁻¹ := by
      rw [← pow_mul, inv_pow, mul_comm]
    rw [hpow] at hlow
    have hpos : 0 < (1 + ‖w‖) ^ (2 * r) := by positivity
    have h1 : ‖(FS : V → ℂ) w‖ ≤ C₂ * ((1 + ‖w‖) ^ (2 * r))⁻¹ := by
      rw [hC₂, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
      exact hFdec w
    exact h1.trans (mul_le_mul_of_nonneg_left hlow hC₂0)
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁0, hcont, hint, fun x => ?_, fun ξ => ?_⟩
  · exact (hpt x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (hft ξ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end S_MeasureTheory_exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport
end P2MW
export P2MW.S_MeasureTheory_exists_forall_norm_le_mul_prod_and_norm_integral_cexp_mul_le_of_contDiff_of_hasCompactSupport (solution)
