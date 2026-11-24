-- Prove2me | solution 1 for GlobalTheory.ChartRing.algebraMap_X_pow_dvd_iff_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:13.053845+00:00
-- url     : https://prove2.me/submissions/7ddac35d-2963-4164-93e2-86cfd45e98e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Theorems.Thm_GlobalTheory_ChartRing_algebraMap_X_pow_dvd_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {O : Type*} [CommRing O] [IsDomain O]
variable (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.AtPrime S (Ideal.span {X} : Ideal O⟦X⟧)]
namespace GlobalTheory.ChartRing
theorem _root_.solution (a : ℕ) (f : O⟦X⟧) :
    algebraMap O⟦X⟧ S X ^ a ∣ algebraMap O⟦X⟧ S f ↔ X ^ a ∣ f :=
  algebraMap_X_pow_dvd_iff _ (fun _ hm => mem_primeCompl_span_X_iff.1 hm) S a f
end GlobalTheory.ChartRing
