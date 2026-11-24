-- Prove2me | solution 1 for GlobalTheory.ExpDivision.hasTemperateGrowth_of_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:42.255198+00:00
-- url     : https://prove2.me/submissions/bc53c6ce-89b5-45bb-acfe-34c51e2c561d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
import Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_of_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖F z‖ ≤ C) :
    (fun t : ℝ => F t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_closed
    {f | ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ R : ℝ, ∃ C : ℝ, ∀ z : ℂ, |z.im| ≤ R → ‖G z‖ ≤ C) ∧
      f = fun t : ℝ => G t} ?_ ?_ ?_ ⟨F, hF, hb, rfl⟩
  · rintro f ⟨G, hG, -, rfl⟩ x
    exact (hG x).hasDerivAt.comp_ofReal.differentiableAt
  · rintro f ⟨G, hG, hB, rfl⟩
    refine ⟨deriv G, hG.deriv, fun R => ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hB (R + 1)
      refine ⟨C / 1, fun z hz => ?_⟩
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hG.diffContOnCl ?_
      intro w hw
      apply hC
      have h1 : ‖w - z‖ = 1 := by simpa [dist_eq_norm] using hw
      have h2 := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, h1] at h2
      have h3 := abs_add_le (w.im - z.im) z.im
      rw [sub_add_cancel] at h3
      linarith
    · funext x
      exact (hG x).hasDerivAt.comp_ofReal.deriv
  · rintro f ⟨G, -, hB, rfl⟩
    obtain ⟨C, hC⟩ := hB 0
    exact ⟨0, C, fun x => by simpa using hC x (by simp)⟩
end GlobalTheory.ExpDivision
