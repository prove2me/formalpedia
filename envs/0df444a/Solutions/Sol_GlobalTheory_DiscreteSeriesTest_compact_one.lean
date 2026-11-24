-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.compact_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:37.887807+00:00
-- url     : https://prove2.me/submissions/e37526a8-6c0d-47e8-824b-1a01ad4a5aed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_norm_entry

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
theorem _root_.solution (ε : Fin 1 → Bool) : CompactSpace (UJ ε) := by
  have hE := (isClosedEmbeddingMatrix 1 ε).1
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin 1 => Set.pi Set.univ fun _ : Fin 1 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine ⟨?_⟩
  have := hE.isCompact_preimage hc
  convert this using 1
  symm
  refine Set.eq_univ_of_forall fun g i _ j _ => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simpa using (norm_entry g.2).le
end GlobalTheory.DiscreteSeriesTest
