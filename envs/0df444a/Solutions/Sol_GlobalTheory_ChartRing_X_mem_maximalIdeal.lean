-- Prove2me | solution 1 for GlobalTheory.ChartRing.X_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:40:45.675536+00:00
-- url     : https://prove2.me/submissions/e3474fc4-1855-4765-b1d2-523af93c608a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsPrincipalIdealRingOfIsLocalization
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ChartRing.evalAdic_C
attribute [local simp] GlobalTheory.ChartRing.evalAdic_X



set_option autoImplicit false
open PowerSeries IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {O : Type*} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.ChartRing
theorem _root_.solution : (X : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ := by
  simp [maximalIdeal_eq_comap]
end GlobalTheory.ChartRing
