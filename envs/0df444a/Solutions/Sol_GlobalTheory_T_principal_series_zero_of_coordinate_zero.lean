-- Prove2me | solution 1 for GlobalTheory.T.principal_series_zero_of_coordinate_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:15.304046+00:00
-- url     : https://prove2.me/submissions/1ac31eb3-22ba-4286-970d-c0faa2a09bad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZeroStatement
import Theorems.Thm_GlobalTheory_PrinTwo_eq_zero_of_ev_one_of_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0 := by
  first | exact @GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord | exact GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord | (intros; apply GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord <;> assumption)
end _root_.GlobalTheory.T
