-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.coef_le_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:23.370415+00:00
-- url     : https://prove2.me/submissions/3ca38983-e609-452a-87e6-5d7f085f53f6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {a β : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hβ0 : β 0 = 1) (hβp : ∀ p, 0 ≤ β p)
    (hβ : ∀ n p, 1 ≤ p → p ≤ n + 1 → (a n)⁻¹ * β (p - 1) ≤ (1 / 2) ^ (n + 1) * β p)
    (n p : ℕ) : coef a n p ≤ β p := by
  have key : ∀ n p, 1 ≤ p → coef a n p ≤ β p * (1 - (1 / 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [coef]
    | succ n ih =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [coef]
      have h1 := ih (q + 1) (by omega)
      have h2 : coef a n q / a n ≤ (1 / 2) ^ (n + 1) * β (q + 1) := by
        rcases Nat.lt_or_ge n q with hq | hq
        · rw [coef_eq_zero a hq, zero_div]
          have := hβ n (q + 1) (by omega)
          have hb : 0 ≤ β (q + 1) := hβp _
          positivity
        · have hc : coef a n q ≤ β q := by
            rcases Nat.eq_zero_or_pos q with rfl | hq0
            · rw [coef_zero_right, hβ0]
            · have := ih q hq0
              have hbq : 0 ≤ β q := hβp q
              nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
          have := hβ n (q + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel] at this
          calc coef a n q / a n = (a n)⁻¹ * coef a n q := by ring
            _ ≤ (a n)⁻¹ * β q := mul_le_mul_of_nonneg_left hc (inv_nonneg.2 (ha n).le)
            _ ≤ _ := this
      calc coef a n (q + 1) + coef a n q / a n
          ≤ β (q + 1) * (1 - (1 / 2) ^ n) + (1 / 2) ^ (n + 1) * β (q + 1) := add_le_add h1 h2
        _ = β (q + 1) * (1 - (1 / 2) ^ (n + 1)) := by ring
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [coef_zero_right, hβ0]
  · have := key n p hp
    nlinarith [hβp p, pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
end GroundTheory.Automorphic.LineKernel
