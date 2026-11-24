-- Prove2me | solution 1 for GlobalTheory.RealWeil.continuous_inner_rho_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:37.077197+00:00
-- url     : https://prove2.me/submissions/5f8732d3-8f28-45f7-9068-f6f01deeadfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply
import Theorems.Thm_GlobalTheory_RealWeil_continuous_pPart
import Theorems.Thm_GlobalTheory_RealWeil_continuous_qPart
import Theorems.Thm_GlobalTheory_RealWeil_coeFn_rho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (φ f : Sch l) :
    Continuous fun w : l ⊕ l → ℝ => ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ := by
  have e : ∀ w : l ⊕ l → ℝ, ⟪φ.toLp 2, rho w (f.toLp 2)⟫_ℂ = ∫ x, starRingEnd ℂ (φ x) * rhoFun w f x := by
    intro w
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2 volume, coeFn_rho w (f.toLp 2),
      rhoFun_congr w (f.coeFn_toLp 2 volume)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp [mul_comm]
  simp only [e]
  refine continuous_of_dominated (bound := fun x => ‖φ x‖ * SchwartzMap.seminorm ℝ 0 0 f) (fun w => ?_)
    (fun w => .of_forall fun x => ?_) ((φ.integrable (μ := volume)).norm.mul_const _) (.of_forall fun x => ?_)
  · exact ((continuous_star.comp φ.continuous).mul
      ((continuous_phase w).mul (f.continuous.comp (continuous_add_const _)))).aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_conj, rhoFun, norm_mul, norm_phase, one_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  · simp only [rhoFun, phase]
    have := continuous_pPart (l := l)
    have := continuous_qPart (l := l)
    fun_prop
end GlobalTheory.RealWeil
