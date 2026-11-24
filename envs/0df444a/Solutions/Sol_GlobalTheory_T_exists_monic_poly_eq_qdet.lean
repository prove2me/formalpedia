-- Prove2me | solution 1 for GlobalTheory.T.exists_monic_poly_eq_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:38.88816+00:00
-- url     : https://prove2.me/submissions/d3492a0e-a70b-4d47-9cfe-8f1dcb4016c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetPolyMapMonic
import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetPolyMapMonicStatement
import Theorems.Thm_GlobalTheory_qdet_polyMap_monic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  first | exact @GlobalTheory.qdet_polyMap_monic | exact GlobalTheory.qdet_polyMap_monic | (intros; apply GlobalTheory.qdet_polyMap_monic <;> assumption)
end _root_.GlobalTheory.T
