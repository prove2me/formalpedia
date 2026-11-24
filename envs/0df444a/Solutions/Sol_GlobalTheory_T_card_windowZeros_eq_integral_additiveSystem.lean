-- Prove2me | solution 1 for GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:02.543102+00:00
-- url     : https://prove2.me/submissions/680fd28e-ce61-4f74-94ef-3ac71a682e59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosEqIntegralAdditiveSystem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosEqIntegralAdditiveSystemStatement
import Theorems.Thm_GlobalTheory_PMonE_winPt_card


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
theorem _root_.solution : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F), (∀ j, π j ≠ 0) → ∀ (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F), (∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) → Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} = Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  first | exact @GlobalTheory.PMonE.winPt_card | exact GlobalTheory.PMonE.winPt_card | (intros; apply GlobalTheory.PMonE.winPt_card <;> assumption)
end _root_.GlobalTheory.T
