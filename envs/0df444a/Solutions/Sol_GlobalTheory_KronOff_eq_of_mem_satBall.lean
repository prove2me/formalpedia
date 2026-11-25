-- Prove2me | solution 1 for GlobalTheory.KronOff.eq_of_mem_satBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:21.708722+00:00
-- url     : https://prove2.me/submissions/6250dee3-8d30-474b-8209-5d219b0ebc26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableIndicatorOfContOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.KronOff
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (δ : ℝ)
    (hδ : Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : x ∈ satBall X x0 δ) :
    ∃ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b := by
  obtain ⟨z, hz, h⟩ := h
  have hc : cpt X x0 z ∈ X.dom := hδ hz
  have hu : ∀ τ, IsUnit (mat (cpt X x0 z) τ).det := fun τ => isUnit_iff_ne_zero.mpr (hc τ).1
  have key : ∀ τ, mat (cpt X x0 z) τ * ((mat (cpt X x0 z) τ)⁻¹ * mat x τ) = mat x τ := fun τ => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  refine ⟨z, hz, fun τ => ((mat (cpt X x0 z) τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ),
    fun τ => ⟨?_, ?_⟩, ?_⟩
  · intro h0
    apply (hx τ).1
    rw [← key τ, Matrix.det_mul]
    exact mul_eq_zero_of_right _ h0
  · intro a c hca
    show ((mat (cpt X x0 z) τ)⁻¹ * mat x τ) a c = 0
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, h τ hca, smul_zero]
  · funext τ
    exact (key τ).symm
end GlobalTheory.KronOff
