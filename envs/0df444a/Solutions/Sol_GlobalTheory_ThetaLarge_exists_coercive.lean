-- Prove2me | solution 1 for GlobalTheory.ThetaLarge.exists_coercive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:16.233804+00:00
-- url     : https://prove2.me/submissions/5a441089-ceb8-41e0-8f37-e61bdb760aaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
import Theorems.Thm_GlobalTheory_ThetaLarge_continuous_form

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
variable {g : ℕ}
namespace GlobalTheory.ThetaLarge
theorem _root_.solution (M : Matrix (Fin g) (Fin g) ℂ)
    (hM : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ M.mulVec (star z)).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin g → ℂ, c * ‖z‖ ^ 2 ≤ (z ⬝ᵥ M.mulVec (star z)).re := by
  obtain ⟨c, hc, h⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_forall_le'
    (continuous_form M).continuousOn (a := 0) fun z hz => hM z (by
      rintro rfl
      simp at hz)
  refine ⟨c, hc, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨u, hu, hzu⟩ : ∃ u : Fin g → ℂ, ‖u‖ = 1 ∧ z = (‖z‖ : ℝ) • u :=
    ⟨‖z‖⁻¹ • z, by rw [norm_smul]; simp [hn.ne'], by simp [smul_smul, hn.ne']⟩
  have h2 := h u (by simpa using hu)
  generalize ‖z‖ = r at hn hzu
  subst hzu
  rw [star_smul, star_trivial, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_re, smul_re,
    smul_eq_mul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg r)]
end GlobalTheory.ThetaLarge
