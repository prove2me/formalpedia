-- Prove2me | solution 1 for GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:30:32.803582+00:00
-- url     : https://prove2.me/submissions/239af62e-dda8-4fa4-9c57-3b60a2fc9571

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_charpoly_overExt_separable


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
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by
  first | exact @GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable | exact GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable | (intros; apply GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable <;> assumption)
end _root_.GlobalTheory.T
