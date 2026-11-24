-- Prove2me | solution 1 for GlobalTheory.ChartRing.addVal_algebraMap_atPrime_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:25.725504+00:00
-- url     : https://prove2.me/submissions/412d5eda-99c1-409d-b1d7-1a54c5e2ff3c

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
variable {O : Type*} [CommRing O] [IsDomain O]
variable (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.AtPrime S (Ideal.span {X} : Ideal O⟦X⟧)]
namespace GlobalTheory.ChartRing
theorem _root_.solution [IsDomain S] [IsDiscreteValuationRing S] (f : O⟦X⟧) :
    IsDiscreteValuationRing.addVal S (algebraMap O⟦X⟧ S f) = f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨u, hu⟩ := associated_X_pow_order_atPrime S hf
  rw [IsDiscreteValuationRing.addVal_def _ u (prime_algebraMap_X_atPrime (O := O) S).irreducible
    _ (by rw [← hu, mul_comm]), coe_toNat_order hf]
end GlobalTheory.ChartRing
