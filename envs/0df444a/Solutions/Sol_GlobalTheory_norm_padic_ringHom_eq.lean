-- Prove2me | solution 1 for GlobalTheory.norm_padic_ringHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:41.457526+00:00
-- url     : https://prove2.me/submissions/641aeb9d-5000-42d3-a340-20fd2bb5a2a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {C : Type*} [NormedField C] (p : ℕ) [hp : Fact p.Prime]
    (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (j : ℚ_[p] →+* C) (hj : ∀ x : ℤ_[p], ‖j x‖ ≤ 1) (x : ℚ_[p]) :
    ‖j x‖ = ‖x‖ := by
  have hu : ∀ y : ℚ_[p], ‖y‖ = 1 → ‖j y‖ = 1 := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have h1 : ‖j y‖ ≤ 1 := hj ⟨y, hy.le⟩
    have h2 : ‖j y⁻¹‖ ≤ 1 := hj ⟨y⁻¹, by simp [hy]⟩
    rw [map_inv₀, norm_inv, inv_le_one₀ (by simpa using hy0)] at h2
    exact le_antisymm h1 h2
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have := hu (x * (p : ℚ_[p]) ^ (-x.valuation)) (by
    rw [norm_mul, norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx, inv_zpow,
      mul_inv_cancel₀ (zpow_ne_zero _ hp0)])
  rw [map_mul, map_zpow₀, map_natCast, norm_mul, norm_zpow, h, inv_zpow,
    mul_inv_eq_one₀ (zpow_ne_zero _ hp0)] at this
  rw [this, Padic.norm_eq_zpow_neg_valuation hx]
end GlobalTheory
