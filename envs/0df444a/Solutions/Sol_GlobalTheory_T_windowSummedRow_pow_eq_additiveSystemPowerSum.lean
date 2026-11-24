-- Prove2me | solution 1 for GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:26:03.485394+00:00
-- url     : https://prove2.me/submissions/026c69b4-f355-4156-b681-a54dfc5c9139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSumStatement
import Theorems.Thm_GlobalTheory_PMonE_rowS_winPt_pow_eq_gsum_coefB


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
theorem _root_.solution : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F) (L U : ℕ), 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h), (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) = gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  first | exact @GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | exact GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | (intros; apply GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB <;> assumption)
end _root_.GlobalTheory.T
