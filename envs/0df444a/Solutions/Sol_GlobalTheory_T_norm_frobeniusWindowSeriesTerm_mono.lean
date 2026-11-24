-- Prove2me | solution 1 for GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:34.055904+00:00
-- url     : https://prove2.me/submissions/8ffad3ea-ef5f-4a51-95dc-a10c5491c8a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMono
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMonoStatement
import Theorems.Thm_GlobalTheory_PMonE_term_norm_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  first | exact @GlobalTheory.PMonE.term_norm_mono | exact GlobalTheory.PMonE.term_norm_mono | (intros; apply GlobalTheory.PMonE.term_norm_mono <;> assumption)
end _root_.GlobalTheory.T
