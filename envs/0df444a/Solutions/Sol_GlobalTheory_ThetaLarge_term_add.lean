-- Prove2me | solution 1 for GlobalTheory.ThetaLarge.term_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:23.87018+00:00
-- url     : https://prove2.me/submissions/89462051-210b-4566-8e37-0dd81ac9a964

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaLarge
variable {E : Type*} [NormedAddCommGroup E]
variable {L : Submodule ℤ E} {H : E → E → ℂ} {χ : L → ℂ}
namespace GlobalTheory.ThetaLarge
theorem _root_.solution (hl : ∀ x y w, H (x + y) w = H x w + H y w)
    (hr : ∀ x y w, H w (x + y) = H w x + H w y) (hs : ∀ x y, H y x = (starRingEnd ℂ) (H x y))
    (h1 : ∀ l, ‖χ l‖ = 1)
    (hχ : ∀ l m : L, χ (l + m) = χ l * χ m * cexp (Real.pi * I * (H l m).im))
    (z₀ : E) (l m : L) (z : E) :
    term L H χ z₀ m (z + l) =
      (χ l * cexp (Real.pi * H z l + Real.pi / 2 * H l l)) * term L H χ z₀ (l + m) z := by
  have hne : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using h1 l
  unfold term
  rw [hχ, mul_inv, mul_inv, ← Complex.exp_neg, Submodule.coe_add, ← add_assoc]
  have e : (Real.pi * H (z + l + m) z₀ - (Real.pi * H (z + l) m + Real.pi / 2 * H m m) : ℂ) =
      (Real.pi * H z l + Real.pi / 2 * H l l) + (-(Real.pi * I * (H l m).im)) +
      (Real.pi * H (z + l + m) z₀ -
        (Real.pi * H z (l + m) + Real.pi / 2 * H (l + m) (l + m))) := by
    rw [hl z l m, hr, hl l m, hr, hr, hs l m]
    have := Complex.sub_conj (H l m)
    push_cast at this
    linear_combination (-(Real.pi : ℂ) / 2) * this
  rw [e, Complex.exp_add, Complex.exp_add]
  have := hne l
  field_simp
end GlobalTheory.ThetaLarge
