-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_of_injective_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:19.647223+00:00
-- url     : https://prove2.me/submissions/2f6da6d1-b67b-4ecd-874b-d96b83b2b437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed S] (φ : R →+* S) (hφ : Function.Injective φ)
    (h : ∀ a b : R, b ≠ 0 → φ b ∣ φ a → b ∣ a) : IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  let ψ : FractionRing R →+* FractionRing S := IsFractionRing.map hφ
  have hψ (r : R) : ψ (algebraMap R _ r) = algebraMap S _ (φ r) :=
    IsLocalization.map_eq _ r
  have hint : IsIntegral S (ψ (algebraMap R _ a / algebraMap R _ b)) :=
    hx.map_of_comp_eq φ ψ (RingHom.ext fun r ↦ (hψ r).symm)
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hb1 : algebraMap S (FractionRing S) (φ b) ≠ 0 := by
    simpa using (map_ne_zero_iff φ hφ).mpr hb0
  rw [map_div₀, hψ, hψ, eq_div_iff hb1, ← map_mul] at hc
  obtain ⟨d, rfl⟩ := h a b hb0 ⟨c, by rw [← IsFractionRing.injective S _ hc, mul_comm]⟩
  refine ⟨d, ?_⟩
  have : algebraMap R (FractionRing R) b ≠ 0 := by simpa using hb0
  rw [map_mul, mul_div_cancel_left₀ _ this]
end GlobalTheory
