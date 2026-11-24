-- Prove2me | solution 1 for GlobalTheory.RealWeil.exists_extension_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:58.665868+00:00
-- url     : https://prove2.me/submissions/2183001f-b8e1-44fa-ad42-1ef2175a2bd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution {V E : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : V →ₗ[ℂ] E) (lam : V →ₗ[ℂ] ℂ) (C : ℝ) (hb : ∀ f, ‖lam f‖ ≤ C * ‖T f‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ f, lam f = Λ (T f) := by
  have hker : LinearMap.ker T ≤ LinearMap.ker lam := fun f hf => by
    have := hb f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let φ : LinearMap.range T →ₗ[ℂ] ℂ := ((LinearMap.ker T).liftQ lam hker) ∘ₗ T.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ f, φ ⟨T f, f, rfl⟩ = lam f := fun f => by
    change (LinearMap.ker T).liftQ lam hker (T.quotKerEquivRange.symm ⟨T f, LinearMap.mem_range_self T f⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range T) (φ.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [hφ]
    exact hb f))
  refine ⟨Λ, fun f => ?_⟩
  rw [← hφ]
  exact (hΛ ⟨T f, f, rfl⟩).symm
end GlobalTheory.RealWeil
