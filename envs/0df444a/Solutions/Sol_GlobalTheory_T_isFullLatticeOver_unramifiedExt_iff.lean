-- Prove2me | solution 1 for GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:10.355797+00:00
-- url     : https://prove2.me/submissions/08de673c-604c-4f25-b294-f9082c994c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIffStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_isLat_overExt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  first | exact @GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isLat_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isLat_overExt_iff <;> assumption)
end _root_.GlobalTheory.T
