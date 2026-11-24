-- Prove2me | solution 1 for GlobalTheory.JR.GLift.unitG_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:10.758365+00:00
-- url     : https://prove2.me/submissions/7b8da143-de3b-4318-ae59-967b0f927cee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockGlBorderedConjugationActionI
import Theorems.Thm_GlobalTheory_JR_GLift_isIntegral_act
import Theorems.Thm_GlobalTheory_JR_GLift_act_inv_act

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F),
    k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  intro F _ _ n k hk Y
  have hk' : k⁻¹ ∈ glO n F := (glOSub n F).inv_mem hk
  have key : IsIntegral (act k Y) ↔ IsIntegral Y :=
    ⟨fun h => act_inv_act k Y ▸ isIntegral_act hk' h, isIntegral_act hk⟩
  have e : ∀ Z : Gl n F, unitG n F Z = Set.indicator {Z | IsIntegral Z} 1 Z := fun _ => rfl
  rw [e, e]
  by_cases h : IsIntegral Y
  · rw [Set.indicator_of_mem (show act k Y ∈ {Z | IsIntegral Z} from key.2 h),
      Set.indicator_of_mem (show Y ∈ {Z | IsIntegral Z} from h)]
    rfl
  · rw [Set.indicator_of_notMem (show act k Y ∉ {Z | IsIntegral Z} from fun h' => h (key.1 h')),
      Set.indicator_of_notMem (show Y ∉ {Z | IsIntegral Z} from h)]
end GlobalTheory.JR.GLift
