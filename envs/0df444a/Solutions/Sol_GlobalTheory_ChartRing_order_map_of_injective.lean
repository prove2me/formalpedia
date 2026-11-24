-- Prove2me | solution 1 for GlobalTheory.ChartRing.order_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:26.614895+00:00
-- url     : https://prove2.me/submissions/bd1f2f75-960e-411a-a35a-91ff245db88d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
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
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {O : Type*} [CommRing O] [IsDomain O] (K : Type*) [Field K] [Algebra O K]
  [IsFractionRing O K]
omit [IsDomain O]
namespace GlobalTheory.ChartRing
theorem _root_.solution {A : Type*} [CommRing A] {φ : O →+* A}
    (hφ : Function.Injective φ) (f : O⟦X⟧) : (f.map φ).order = f.order :=
  le_antisymm (le_order _ _ fun i hi => hφ (by simpa using coeff_of_lt_order i hi))
    (le_order_map φ)
end GlobalTheory.ChartRing
