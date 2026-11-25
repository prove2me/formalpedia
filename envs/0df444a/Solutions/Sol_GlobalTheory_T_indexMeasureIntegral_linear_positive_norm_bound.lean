-- Prove2me | solution 1 for GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:17:47.851803+00:00
-- url     : https://prove2.me/submissions/2edcda6e-a012-41ed-8c43-7f0c5544f4de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBound
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Theorems.Thm_GlobalTheory_IdxInt_Lin_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, Nice A φ → Nice A ψ → Nice A (φ + ψ) ∧ cint A (φ + ψ) = cint A φ + cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖cint A φ‖ ≤ (cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), Nice A φ → Nice A (fun w => c * φ w) ∧ cint A (fun w => c * φ w) = c * cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (cint A (ind P)).re ∧ (cint A (ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, Nice A (φ i)) → Nice A (fun w => ∑ i ∈ s, φ i w) ∧ cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, cint A (φ i) := by
  first | exact @GlobalTheory.IdxInt.Lin.main | exact GlobalTheory.IdxInt.Lin.main | (intros; apply GlobalTheory.IdxInt.Lin.main <;> assumption)
end _root_.GlobalTheory.T
