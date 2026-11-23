-- Prove2me | solution 1 for GlobalTheory.RealWeil.Good.fourier
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:51.314863+00:00
-- url     : https://prove2.me/submissions/5bcfe769-c458-4081-b5f9-ec9ac892b0ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Theorems.Thm_GlobalTheory_RealWeil_proj_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
variable {J : V ≃ₗᵢ[ℝ] V}
namespace GlobalTheory.RealWeil
namespace Good
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) (n : ℕ) :
    Integrable fun w => ‖w‖ ^ n * ‖𝓕 (fun u => gau u • ρ u f) w‖ := by
  have := hf n
  simp only [proj_translate hJ, h.2.2.1] at this
  rw [← J.measurePreserving.integrable_comp_emb J.toHomeomorph.measurableEmbedding]
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp
end Good
end GlobalTheory.RealWeil
