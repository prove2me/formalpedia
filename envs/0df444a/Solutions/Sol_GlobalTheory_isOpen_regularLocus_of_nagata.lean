-- Prove2me | solution 1 for GlobalTheory.isOpen_regularLocus_of_nagata
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:16.608666+00:00
-- url     : https://prove2.me/submissions/b14686db-bf46-40fb-ad0c-6c63d28e2968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagata
import Theorems.Thm_GlobalTheory_isRegularLocalRing_atPrime_of_le
import Theorems.Thm_GlobalTheory_T_exists_regular_near_of_regular_quotient_prime
import Theorems.Thm_GlobalTheory_T_isOpen_of_stableUnderGeneralization_of_locally_open


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  intro B _ _ hyp
  apply GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open B
  · intro p q hpq hq
    exact isRegularLocalRing_atPrime_of_le p.asIdeal q.asIdeal hpq hq
  · intro p hp
    obtain ⟨g₁, hg₁p, hg₁⟩ := hyp p.asIdeal
    obtain ⟨g₂, hg₂p, hg₂⟩ := GlobalTheory.T.exists_regular_near_of_regular_quotient_prime B p.asIdeal hp
    refine ⟨g₁ * g₂, fun h => (p.isPrime.mem_or_mem h).elim hg₁p hg₂p, ?_⟩
    intro q hpq hq
    have hq₁ : g₁ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_right _ h)
    have hq₂ : g₂ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_left _ h)
    exact hg₂ q.asIdeal hpq hq₂ (hg₁ q.asIdeal hpq hq₁)
end GlobalTheory
