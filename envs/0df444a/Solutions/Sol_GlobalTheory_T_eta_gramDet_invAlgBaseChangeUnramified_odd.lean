-- Prove2me | solution 1 for GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:34.897066+00:00
-- url     : https://prove2.me/submissions/7ec39526-2aff-4bea-982d-05d17559daed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_eta_overExt


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
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (x : B.Aˣ), B.σ (x : B.A) = x → K'.eta ((overExt φ B ψ hψ hσ).gramDet (x : B.A)) = K.eta (B.gramDet (x : B.A)) := by
  first | exact @GlobalTheory.UnitLemma.Unr.eta_overExt | exact GlobalTheory.UnitLemma.Unr.eta_overExt | (intros; apply GlobalTheory.UnitLemma.Unr.eta_overExt <;> assumption)
end _root_.GlobalTheory.T
