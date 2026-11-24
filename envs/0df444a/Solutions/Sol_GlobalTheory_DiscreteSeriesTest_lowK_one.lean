-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.lowK_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:39.316333+00:00
-- url     : https://prove2.me/submissions/763236d9-9e63-42d4-ae66-9aa13d263465

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.DiscreteSeriesTest
namespace GlobalTheory.DiscreteSeriesTest
theorem _root_.solution (ε : Fin 1 → Bool) (lam : Fin 1 → ℝ) : lowK ε lam = lam := by
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  simp [lowK, rhoN, rhoC, Finset.filter_singleton]
end GlobalTheory.DiscreteSeriesTest
