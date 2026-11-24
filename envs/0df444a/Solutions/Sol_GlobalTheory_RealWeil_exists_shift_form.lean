-- Prove2me | solution 1 for GlobalTheory.RealWeil.exists_shift_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:59.460804+00:00
-- url     : https://prove2.me/submissions/55ebe5a9-fad3-47da-9815-7032c210b801

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : V ≃ₗᵢ[ℝ] V) (v : V) :
    ∃ l : V →L[ℝ] ℂ, ‖l‖ ≤ 2 * π * ‖v‖ ∧
      ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (omJ J v t : ℂ) := by
  let l : V →L[ℝ] ℂ := (-(π : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ v)) -
      ((π : ℂ) * I) • (Complex.ofRealCLM.comp ((innerSL ℝ v).comp (J : V →L[ℝ] V)))
  have hl : ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ) := fun t => by
    simp [l]
  refine ⟨l, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_, fun t => by
    rw [hl t]; rfl⟩
  rw [hl t]
  calc ‖-(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ)‖
      ≤ ‖-(π : ℂ) * (⟪v, t⟫ : ℝ)‖ + ‖(π : ℂ) * I * (⟪v, J t⟫ : ℝ)‖ := norm_sub_le _ _
    _ = π * |⟪v, t⟫| + π * |⟪v, J t⟫| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    _ ≤ π * (‖v‖ * ‖t‖) + π * (‖v‖ * ‖t‖) := by
        gcongr
        · exact abs_real_inner_le_norm _ _
        · exact (abs_real_inner_le_norm v (J t)).trans (by rw [J.norm_map])
    _ = 2 * π * ‖v‖ * ‖t‖ := by ring
end GlobalTheory.RealWeil
