-- Prove2me | solution 1 for GlobalTheory.CompactRep.inner_integral_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:58.766335+00:00
-- url     : https://prove2.me/submissions/9b9af92f-e577-4826-aba8-c4ff0a52b012

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}
namespace GlobalTheory.CompactRep
theorem _root_.solution {w : X → H} (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ)
    (x y : H) : ⟪y, (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) x⟫_ℂ =
      ∫ k, ⟪w k, x⟫_ℂ * ⟪y, w k⟫_ℂ ∂μ := by
  have hix : Integrable (fun k => rankOne ℂ (w k) (w k) x) μ :=
    (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
  rw [ContinuousLinearMap.integral_apply hFi x, ← integral_inner hix y]
  simp only [rankOne_apply, inner_smul_right]
end GlobalTheory.CompactRep
