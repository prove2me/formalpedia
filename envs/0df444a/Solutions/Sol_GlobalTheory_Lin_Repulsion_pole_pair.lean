-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.pole_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:45.916637+00:00
-- url     : https://prove2.me/submissions/7fc1ba09-40c9-44a5-b682-e7588866f200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Theorems.Thm_GlobalTheory_Lin_Repulsion_norm_pow_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution {β t : ℝ} (hβ : β < 1) (j : ℕ) :
    ‖1 / ((2 : ℂ) + t * I - 1) ^ j - (1 / ((2 : ℂ) + t * I - β)) ^ j‖ ≤ j * (1 - β) := by
  have h1 : 1 ≤ ‖(2 : ℂ) + t * I - 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm _); simp; norm_num
  have h2 : 1 ≤ ‖(2 : ℂ) + t * I - β‖ := by
    refine le_trans ?_ (Complex.re_le_norm _); simp; linarith
  have n1 : (2 : ℂ) + t * I - 1 ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
  have n2 : (2 : ℂ) + t * I - β ≠ 0 := by intro h; rw [h] at h2; norm_num at h2
  have ha : ‖1 / ((2 : ℂ) + t * I - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]; exact div_le_one_of_le₀ h1 (norm_nonneg _)
  have hb : ‖1 / ((2 : ℂ) + t * I - β)‖ ≤ 1 := by
    rw [norm_div, norm_one]; exact div_le_one_of_le₀ h2 (norm_nonneg _)
  rw [← one_div_pow]
  refine (norm_pow_sub_le ha hb j).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have e : 1 / ((2 : ℂ) + t * I - 1) - 1 / ((2 : ℂ) + t * I - β) =
      ((1 - β : ℝ) : ℂ) * (1 / ((2 : ℂ) + t * I - 1)) * (1 / ((2 : ℂ) + t * I - β)) := by
    push_cast; field_simp; ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  calc _ ≤ (1 - β) * 1 * 1 := by gcongr
    _ = _ := by ring
end GlobalTheory.Lin.Repulsion
