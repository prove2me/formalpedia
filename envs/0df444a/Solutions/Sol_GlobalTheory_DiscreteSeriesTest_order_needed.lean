-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.order_needed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:57.840764+00:00
-- url     : https://prove2.me/submissions/79957f4d-7122-45a5-a44b-27904787a2da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_rhoN_add_rhoC

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
theorem _root_.solution :
    lowK ![true, false] ![1 / 2, 7 / 2] = lowK ![false, true] ![5 / 2, 3 / 2] ∘ Equiv.swap 0 1 := by
  have c : ∀ (ε : Fin 2 → Bool) (a : Fin 2), ε 0 ≠ ε 1 →
      rhoN ε a - rhoC ε a = 1 / 2 - a := by
    intro ε a h
    have h0 : rhoC ε a = 0 := by
      have e1 : (univ.filter fun b => a < b ∧ ε b = ε a) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun b _ hb => ?_
        fin_cases a <;> fin_cases b <;> simp_all
      have e2 : (univ.filter fun b => b < a ∧ ε b = ε a) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun b _ hb => ?_
        fin_cases a <;> fin_cases b <;> simp_all
      simp [rhoC, e1, e2]
    have h1 := rhoN_add_rhoC ε a
    push_cast at h1
    linarith
  funext a
  have h1 := c ![true, false] a (by simp)
  have h2 := c ![false, true] (Equiv.swap 0 1 a) (by simp)
  simp only [lowK, Function.comp_apply, Pi.sub_apply, Pi.add_apply, add_sub_assoc, h1, h2]
  fin_cases a <;> simp <;> norm_num
end GlobalTheory.DiscreteSeriesTest
