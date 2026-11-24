-- Prove2me | solution 1 for GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:14.074377+00:00
-- url     : https://prove2.me/submissions/e87e19b5-1230-4d6a-8741-00bae9f905a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuterStatement
import Theorems.Thm_GlobalTheory_PMonE_win_inner


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
theorem _root_.solution : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F), ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F, Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} = Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  first | exact @GlobalTheory.PMonE.win_inner | exact GlobalTheory.PMonE.win_inner | (intros; apply GlobalTheory.PMonE.win_inner <;> assumption)
end _root_.GlobalTheory.T
