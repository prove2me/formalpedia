-- Prove2me | solution 1 for GlobalTheory.JR.UnitGLift.unitG_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:24.18568+00:00
-- url     : https://prove2.me/submissions/55e16cda-5fb1-45b3-a365-a4124a97a635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
import Theorems.Thm_GlobalTheory_JR_UnitGLift_norm_full_le_one_iff
import Theorems.Thm_GlobalTheory_JR_UnitGLift_norm_eL_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnitGLift
namespace GlobalTheory.JR.UnitGLift
theorem _root_.solution : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 →
    unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  intro F _ r Z μ l hμ
  have hb : ∀ i, ‖(μ • GlobalTheory.JR.Step.eL r F) i‖ ≤ 1 := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ hμ (norm_nonneg _) (norm_eL_le_one i)
  have hmem : GlobalTheory.JR.Step.lift Z μ l ∈
      {Y : Gl (r + 1) F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} ↔
      (Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
        ∧ ‖l‖ ≤ 1) := by
    simp only [Set.mem_setOf_eq, GlobalTheory.JR.Step.lift]
    rw [norm_full_le_one_iff]
    exact ⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨h1, hb, norm_eL_le_one, h4⟩⟩
  unfold unitG
  by_cases hZ : Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
  · by_cases hl : ‖l‖ ≤ 1
    · rw [Set.indicator_of_mem (hmem.2 ⟨hZ, hl⟩), Set.indicator_of_mem hZ, if_pos hl]
      simp
    · rw [Set.indicator_of_notMem (fun h => hl (hmem.1 h).2), if_neg hl, zero_mul]
  · rw [Set.indicator_of_notMem (fun h => hZ (hmem.1 h).1), Set.indicator_of_notMem hZ, mul_zero]
end GlobalTheory.JR.UnitGLift
