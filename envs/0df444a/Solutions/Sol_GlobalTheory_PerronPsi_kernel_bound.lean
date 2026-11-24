-- Prove2me | solution 1 for GlobalTheory.PerronPsi.kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:29:47.380811+00:00
-- url     : https://prove2.me/submissions/15afc54a-5721-4b7d-a813-5b38e0025306

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Theorems.Thm_GlobalTheory_PerronKernel_truncated_perron_kernel
import Theorems.Thm_GlobalTheory_PerronKernel_vinv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ y c T : ℝ, 0 < y → 0 < c → 1 ≤ T →
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      - (if 1 ≤ y then 1 else 0)‖ ≤ C * y ^ c ∧
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      - (if 1 ≤ y then 1 else 0)‖ * (T * |Real.log y|) ≤ C * y ^ c := by
  obtain ⟨C, hC, hK⟩ := GlobalTheory.PerronKernel.truncated_perron_kernel
  refine ⟨max C 1, lt_max_of_lt_right one_pos, ?_⟩
  intro y c T hy hc hT
  have hyc : 0 < y ^ c := Real.rpow_pos_of_pos hy c
  by_cases hy1 : y = 1
  · subst hy1
    have hI : ∫ t in (-T)..T, ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
        = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
      rw [← GlobalTheory.PerronKernel.vinv hc.ne' T]
      congr 1
      ext t
      rw [Complex.ofReal_one, Complex.one_cpow, one_div]
    have ha0 : 0 < Real.arctan (T / c) := Real.arctan_pos.2 (by positivity)
    have ha1 : Real.arctan (T / c) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hpi := Real.pi_pos
    have hE : ‖(1 / (2 * Real.pi) : ℂ) * ((2 * Real.arctan (T / c) : ℝ) : ℂ)
        - (if (1 : ℝ) ≤ 1 then 1 else 0)‖ ≤ 1 := by
      rw [if_pos le_rfl]
      have hre : (1 / (2 * Real.pi) : ℂ) * ((2 * Real.arctan (T / c) : ℝ) : ℂ) - 1
          = ((Real.arctan (T / c) / Real.pi - 1 : ℝ) : ℂ) := by
        push_cast
        field_simp
      rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h1 : 0 ≤ Real.arctan (T / c) / Real.pi := div_nonneg ha0.le hpi.le
      have h2 : Real.arctan (T / c) / Real.pi ≤ 1 := by
        rw [div_le_one hpi]
        linarith
      constructor <;> linarith
    rw [hI]
    refine ⟨?_, ?_⟩
    · calc _ ≤ (1 : ℝ) := hE
        _ ≤ max C 1 * (1 : ℝ) ^ c := by
          rw [Real.one_rpow, mul_one]
          exact le_max_right _ _
    · rw [Real.log_one, abs_zero, mul_zero, mul_zero]
      positivity
  · have hif : (if 1 ≤ y then (1 : ℂ) else 0) = (if 1 < y then 1 else 0) := by
      by_cases h : 1 < y
      · simp [h, h.le]
      · have h' : ¬ 1 ≤ y := fun h' => h (lt_of_le_of_ne h' (Ne.symm hy1))
        simp [h, h']
    have hK' := hK y c T hy hy1 hc hT
    rw [hif]
    have hL : 0 < T * |Real.log y| :=
      mul_pos (by linarith) (abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hy hy1))
    have hC' : C ≤ max C 1 := le_max_left _ _
    refine ⟨?_, ?_⟩
    · calc _ ≤ C * y ^ c * min 1 (1 / (T * |Real.log y|)) := hK'
        _ ≤ C * y ^ c * 1 := by gcongr; exact min_le_left _ _
        _ ≤ max C 1 * y ^ c := by rw [mul_one]; gcongr
    · calc _ ≤ C * y ^ c * min 1 (1 / (T * |Real.log y|)) * (T * |Real.log y|) :=
            mul_le_mul_of_nonneg_right hK' hL.le
        _ ≤ C * y ^ c * (1 / (T * |Real.log y|)) * (T * |Real.log y|) := by
          gcongr
          exact min_le_right _ _
        _ = C * y ^ c := by rw [mul_assoc, one_div_mul_cancel hL.ne', mul_one]
        _ ≤ max C 1 * y ^ c := by gcongr
end GlobalTheory.PerronPsi
