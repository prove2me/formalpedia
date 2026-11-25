-- Prove2me | solution 1 for GlobalTheory.KronOff.rmul_mem_satBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:02:04.772799+00:00
-- url     : https://prove2.me/submissions/d43a8c2b-4fd8-409e-bf13-877bce816d5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableIndicatorOfContOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem mat_rmul_torus_haar_measure {r : ℕ} {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ := by
  ext a c
  rfl
private theorem mat_blockTriangular_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
end
end GlobalTheory.KronOff
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.KronOff
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (δ : ℝ) {x b : Frame X.Ψ r}
    (hx : x ∈ satBall X x0 δ) (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ satBall X x0 δ := by
  obtain ⟨z, hz, h⟩ := hx
  refine ⟨z, hz, fun τ => ?_⟩
  rw [mat_rmul_torus_haar_measure, ← Matrix.mul_assoc]
  exact (h τ).mul (mat_blockTriangular_of_mem_bor hb τ)
end GlobalTheory.KronOff
