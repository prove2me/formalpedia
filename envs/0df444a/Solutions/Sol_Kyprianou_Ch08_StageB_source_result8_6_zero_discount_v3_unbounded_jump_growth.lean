-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_jump_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:33:46.222048+00:00
-- url     : https://prove2.me/submissions/6b73e77f-407f-4b7f-9065-175209ff302e

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_compensated_integrable
import Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_mono
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem solution
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂μ) = ⊤) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧ ∀ θ : ℝ, β ≤ θ →
      C < ∫ y in Ioo (-1 : ℝ) 0, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ := by
  intro C
  let ν : Measure ℝ := μ.restrict (Ioo (-1 : ℝ) 0)
  let J : ℝ → ℝ := fun θ => ∫ y, (Real.exp (θ * y) - 1 - θ * y) / θ ∂ν
  have hneg : ∀ᵐ y ∂ν, y < 0 := by
    dsimp [ν]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun y hy => hy.2)
  have htop : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν) = ⊤ := by
    simpa [ν] using hinf
  have hint : ∀ θ : ℝ, 0 < θ → Integrable (fun y : ℝ =>
      (Real.exp (θ * y) - 1 - θ * y) / θ) ν := by
    intro θ hθ
    have hcomp := Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_compensated_integrable
      μ hμ θ hθ.le
    refine ((hcomp.mono_set (by
      intro y hy
      simpa using hy.2)).const_mul θ⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy.1, lt_trans hy.2 zero_lt_one⟩
    simp [Set.indicator_of_mem hmem, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hintN : ∀ n : ℕ, Integrable (fun y : ℝ =>
      (Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) /
        ((n : ℝ) + 1)) ν := by
    intro n
    exact hint ((n : ℝ) + 1) (by positivity)
  have hJlim : Tendsto (fun n : ℕ => J ((n : ℝ) + 1)) atTop atTop := by
    simpa [J] using
      (AvramDividend.Classical.negative_compensated_real_integral_tendsto_atTop
        ν hneg htop hintN)
  have hJmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → J θ₁ ≤ J θ₂ := by
    intro θ₁ θ₂ hθ₁ hle
    exact AvramDividend.Classical.negative_compensated_integral_mono
      ν θ₁ θ₂ hθ₁ hle hneg (hint θ₁ hθ₁) (hint θ₂ (lt_of_lt_of_le hθ₁ hle))
  have hJeve : ∀ᶠ n : ℕ in atTop, C < J ((n : ℝ) + 1) :=
    hJlim.eventually (eventually_gt_atTop C)
  rcases eventually_atTop.1 hJeve with ⟨N, hN⟩
  refine ⟨(N : ℝ) + 1, by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N)), ?_⟩
  intro θ hθβ
  have hβpos : 0 < (N : ℝ) + 1 := by positivity
  have hmono := hJmono ((N : ℝ) + 1) θ hβpos hθβ
  have hNval := hN N le_rfl
  simpa [J, ν] using (lt_of_lt_of_le hNval hmono)
