-- Prove2me | solution 1 for GlobalTheory.RealWeil.contDiff_gau_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:52.100868+00:00
-- url     : https://prove2.me/submissions/49620314-07aa-481f-840b-c1eed6744ba0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau

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
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.RealWeil
theorem _root_.solution : ContDiff ℝ ∞ fun u : V => (gau u)⁻¹ := by
  have : (fun u : V => (gau u)⁻¹) = fun u => cexp ((π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    rw [gau, ← Complex.exp_neg]
    push_cast
    ring_nf
  rw [this]
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)))
end GlobalTheory.RealWeil
