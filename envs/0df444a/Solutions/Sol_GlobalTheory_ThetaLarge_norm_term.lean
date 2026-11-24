-- Prove2me | solution 1 for GlobalTheory.ThetaLarge.norm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:20.597572+00:00
-- url     : https://prove2.me/submissions/21dfa884-8c80-4b32-9dd7-268641fb7964

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
    (h1 : ∀ l, ‖χ l‖ = 1) (z₀ : E) (l : L) (z : E) :
    ‖term L H χ z₀ l z‖ = Real.exp (π / 2 * ((H z z).re + (H z₀ z₀).re)) *
      Real.exp (-(π / 2) * (H (l + (z - z₀)) (l + (z - z₀))).re) := by
  unfold term
  rw [norm_mul, norm_inv, h1, inv_one, one_mul, Complex.norm_exp, ← Real.exp_add]
  congr 1
  obtain ⟨u, rfl⟩ : ∃ u, z = u + z₀ := ⟨z - z₀, by simp⟩
  rw [add_sub_cancel_right]
  have hs' : ∀ x y, (H y x).re = (H x y).re := fun x y => by rw [hs]; simp
  have e : (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [e, hl, hr, add_re, sub_re, re_ofReal_mul]
  rw [hs' u z₀, hs' u l, hs' z₀ l]
  ring
end GlobalTheory.ThetaLarge
