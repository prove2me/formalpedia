-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:23.367936+00:00
-- url     : https://prove2.me/submissions/08b76c3c-1142-482b-b68f-efe3961478f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegralOfForallMemDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_of_valuationSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] (t : K), (∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ s : S, algebraMap S K s ∈ V) → t ∈ V) → IsIntegral S t := by
  intro S K _ _ _ _ _ _ t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType S K := .of_isLocalization K (nonZeroDivisors S)
  have hic : IsIntegrallyClosedIn (integralClosure S K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure S K) K)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure S K).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_of_valuationSubring (R := S) W
    (fun r => hW ((integralClosure S K).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  exact (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left ht0 (ht V h1 h2)
end GlobalTheory
