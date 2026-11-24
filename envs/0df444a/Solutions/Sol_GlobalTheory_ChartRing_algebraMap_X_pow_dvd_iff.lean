-- Prove2me | solution 1 for GlobalTheory.ChartRing.algebraMap_X_pow_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:11.351614+00:00
-- url     : https://prove2.me/submissions/492745b7-b254-473c-999f-d2a3b0eca8d9

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
namespace GlobalTheory.ChartRing
theorem _root_.solution (M : Submonoid O⟦X⟧) (hM : ∀ m ∈ M, constantCoeff m ≠ 0)
    (S : Type*) [CommRing S] [Algebra O⟦X⟧ S] [IsLocalization M S] (a : ℕ) (f : O⟦X⟧) :
    algebraMap O⟦X⟧ S X ^ a ∣ algebraMap O⟦X⟧ S f ↔ X ^ a ∣ f := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun h => by simpa using map_dvd (algebraMap O⟦X⟧ S) h⟩
  obtain ⟨⟨g, s⟩, hgs⟩ := IsLocalization.surj M z
  have h1 : algebraMap O⟦X⟧ S (f * s) = algebraMap O⟦X⟧ S (X ^ a * g) := by
    rw [map_mul, map_mul, map_pow, hz, mul_assoc, hgs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 h1
  have h2 : X ^ a ∣ ((c * s : M) : O⟦X⟧) * f := ⟨c * g, by
    rw [Submonoid.coe_mul]; linear_combination hc⟩
  exact X_prime.pow_dvd_of_dvd_mul_left a (X_dvd_iff.not.2 (hM _ (c * s).2)) h2
end GlobalTheory.ChartRing
