-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:39:03.426265+00:00
-- url     : https://prove2.me/submissions/0ee3993c-9d0c-4802-93f9-ed9fae94960c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralUnramifiedExtIffIsIntegralBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralUnramifiedExtIffIsIntegralBaseStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_isIntegral_overExt_iff


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
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (a : B.A), @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  first | exact @GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff <;> assumption)
end _root_.GlobalTheory.T
