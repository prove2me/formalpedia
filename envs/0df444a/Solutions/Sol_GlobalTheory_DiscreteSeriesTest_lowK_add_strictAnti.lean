-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.lowK_add_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:54.058657+00:00
-- url     : https://prove2.me/submissions/46f6f4b8-0b06-4dee-a4c5-9cb6eb5c62fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_lowK_add

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) {lam : Fin n → ℝ} (h : StrictAnti lam) :
    StrictAnti (lowK ε lam + (2 : ℝ) • rhoC ε) := by
  intro a b hab
  rw [lowK_add, lowK_add]
  have h1 := h hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith
end GlobalTheory.DiscreteSeriesTest
