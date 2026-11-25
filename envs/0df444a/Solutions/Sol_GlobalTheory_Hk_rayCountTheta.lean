-- Prove2me | solution 1 for GlobalTheory.Hk.rayCountTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:13.335704+00:00
-- url     : https://prove2.me/submissions/19ddf454-3b9d-48e8-9524-a6dbcdd56666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayCountThetaFibreCount
import Theorems.Thm_GlobalTheory_Hk_rayCountTheta_fibre_count
import Theorems.Thm_GlobalTheory_Hk_rayCountTheta_fibre_tsum
import Theorems.Thm_GlobalTheory_T_abs_ncard_qForm_le_sub_pi_div_sqrt_mul_le_ten_sqrt
import Theorems.Thm_GlobalTheory_T_rayClassIdealCount_eq_ncard_shiftedBinaryForm
import Theorems.Thm_GlobalTheory_T_summable_and_abs_tsum_exp_neg_qForm_sub_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, (∀ y : ℝ, 1 ≤ y → |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) * y| ≤ 10 * Real.sqrt y) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) / t| ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 * t := by
  intro K _ _ d M x hd hd4 hd100 hx hK hM D g
  obtain ⟨α, γ, l, θ₁, θ₂, hα, hγ, hαγ, hQ, ha⟩ := GlobalTheory.T.rayClassIdealCount_eq_ncard_shiftedBinaryForm K d M x hd hd4 hd100 hx hK hM D g
  choose q hq1 hq using hQ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hC : Real.pi / Real.sqrt (α * γ) = 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) := by
    have hs : Real.sqrt (α * γ) = Real.sqrt d * (M : ℝ) ^ 2 / 2 := by
      rw [hαγ, show (d : ℝ) * (M : ℝ) ^ 4 / 4 = (Real.sqrt d * (M : ℝ) ^ 2 / 2) ^ 2 by
        rw [div_pow, mul_pow, Real.sq_sqrt hd0.le]; ring]
      exact Real.sqrt_sq (by positivity)
    have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
    rw [hs]
    field_simp
  refine ⟨fun y hy => ?_, fun t ht0 ht1 => ?_⟩
  · have h94 := GlobalTheory.T.abs_ncard_qForm_le_sub_pi_div_sqrt_mul_le_ten_sqrt α γ l θ₁ θ₂ y hα hγ hy
    have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n =
        (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ y}.ncard : ℕ) : ℝ) := by
      simp only [ha]
      exact rayCountTheta_fibre_count (qForm α γ l θ₁ θ₂) q hq1 hq y hy h94.1
    rw [hsum, ← hC]
    exact h94.2
  · have h96 := GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le α γ l θ₁ θ₂ t (by linarith) (by linarith) ht0
    have htsum : ∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) =
        ∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) := by
      simp only [ha]
      exact rayCountTheta_fibre_tsum (qForm α γ l θ₁ θ₂) q hq t h96.1
    rw [htsum, ← hC]
    refine le_trans h96.2 ?_
    have hA : α ≤ α * γ := by nlinarith
    have hG : γ ≤ α * γ := by nlinarith
    have hP1 : 1 ≤ α * γ := by nlinarith
    have hsq : 1 ≤ Real.sqrt (α * γ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hP1
    have hsq0 : 0 < Real.sqrt (α * γ) := by linarith
    have hCπ : Real.pi / Real.sqrt (α * γ) ≤ Real.pi := div_le_self Real.pi_pos.le hsq
    have hC0 : 0 ≤ Real.pi / Real.sqrt (α * γ) := by positivity
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have key : 3 * Real.pi * (α * γ) ^ 2 ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 := by
      rw [hαγ]
      have h1 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 10 := pow_le_pow_right₀ hd1 (by norm_num)
      have h2 : (M : ℝ) ^ 8 ≤ (M : ℝ) ^ 20 := pow_le_pow_right₀ hM1 (by norm_num)
      have hX : 0 ≤ (d : ℝ) ^ 10 * (M : ℝ) ^ 20 := by positivity
      calc 3 * Real.pi * ((d : ℝ) * (M : ℝ) ^ 4 / 4) ^ 2
          = (3 * Real.pi / 16) * ((d : ℝ) ^ 2 * (M : ℝ) ^ 8) := by ring
        _ ≤ 1 * ((d : ℝ) ^ 10 * (M : ℝ) ^ 20) :=
          mul_le_mul (by linarith [Real.pi_le_four]) (mul_le_mul h1 h2 (by positivity) (by positivity))
            (by positivity) (by norm_num)
        _ ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 := by
          rw [show (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 = 4 ^ 10 * ((d : ℝ) ^ 10 * (M : ℝ) ^ 20) by ring]
          linarith
    have hpoly : α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2 ≤ 3 * (α * γ) ^ 2 := by
      have e1 : α ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ (by linarith) hA 2
      have e2 : γ ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ (by linarith) hG 2
      have ht2 : t ^ 2 ≤ 1 := by nlinarith
      have e3 : α ^ 2 * γ ^ 2 * t ^ 2 ≤ (α * γ) ^ 2 := by
        calc α ^ 2 * γ ^ 2 * t ^ 2 = (α * γ) ^ 2 * t ^ 2 := by ring
          _ ≤ (α * γ) ^ 2 * 1 := mul_le_mul_of_nonneg_left ht2 (by positivity)
          _ = (α * γ) ^ 2 := by ring
      linarith
    calc Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2)
        = Real.pi / Real.sqrt (α * γ) * t * (α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2) := by
          field_simp
      _ ≤ Real.pi * t * (3 * (α * γ) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCπ ht0.le) hpoly (by positivity) (by positivity)
      _ = 3 * Real.pi * (α * γ) ^ 2 * t := by ring
      _ ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 * t := mul_le_mul_of_nonneg_right key ht0.le
end GlobalTheory.Hk
