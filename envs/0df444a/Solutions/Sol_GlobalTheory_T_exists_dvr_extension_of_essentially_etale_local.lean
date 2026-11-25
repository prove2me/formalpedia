-- Prove2me | solution 1 for GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:15.072248+00:00
-- url     : https://prove2.me/submissions/628ed113-fb4a-46a6-915d-88f401d5315d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrExtensionOfEssentiallyEtaleLocalStatement
import Theorems.Thm_GlobalTheory_exists_valuationSubring_extend_of_formallyEtale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K K' R S : Type} [Field K] [Field K'] [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [IsLocalRing R] [IsLocalRing S] [Algebra R K] [Algebra S K'] [IsFractionRing R K] [IsFractionRing S K'] (φ : K →+* K') (σ : R →+* S) [IsLocalHom σ], σ.Flat → σ.FormallyEtale → σ.EssFiniteType → φ.comp (algebraMap R K) = (algebraMap S K').comp σ → ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ a, algebraMap R K a ∈ V) → ∃ (V' : ValuationSubring K') (h : ∀ x ∈ V, φ x ∈ V'), IsDiscreteValuationRing V' ∧ (∀ b, algebraMap S K' b ∈ V') ∧ (∀ x, φ x ∈ V' → x ∈ V) ∧ (φ.restrict V V' h).FormallyEtale ∧ (φ.restrict V V' h).EssFiniteType := by
  first | exact @GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | exact GlobalTheory.exists_valuationSubring_extend_of_formallyEtale | (intros; apply GlobalTheory.exists_valuationSubring_extend_of_formallyEtale <;> assumption)
end _root_.GlobalTheory.T
