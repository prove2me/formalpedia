-- Prove2me | solution 1 for GlobalTheory.ChartRing.comap_span_X_pow_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:57:20.508973+00:00
-- url     : https://prove2.me/submissions/8f5cdd3f-44de-49f7-9d35-a3564d6d31f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Theorems.Thm_GlobalTheory_ChartRing_algebraMap_X_pow_dvd_iff_atPrime

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
theorem _root_.solution (a : ℕ) :
    (Ideal.span {algebraMap O⟦X⟧ S X ^ a}).comap (algebraMap O⟦X⟧ S) = Ideal.span {X ^ a} := by
  ext f
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    algebraMap_X_pow_dvd_iff_atPrime]
end GlobalTheory.ChartRing
