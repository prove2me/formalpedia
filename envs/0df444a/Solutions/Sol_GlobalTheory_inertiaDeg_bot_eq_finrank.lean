-- Prove2me | solution 1 for GlobalTheory.inertiaDeg_bot_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:00:12.197172+00:00
-- url     : https://prove2.me/submissions/f60f5940-53b4-4cc0-b69c-4c888a601527

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertiaDegBotEqFinrankFiniteDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by
  intro R S _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hinj
  haveI : (⊥ : Ideal S).LiesOver (⊥ : Ideal R) :=
    ⟨(Ideal.comap_bot_of_injective (algebraMap R S) hinj).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal R) (⊥ : Ideal S)
  rw [Ideal.inertiaDeg_eq (⊥ : Ideal R) (⊥ : Ideal S)]
  exact IsFractionRing.finrank_eq R (⊥ : Ideal R).ResidueField S
    (⊥ : Ideal S).ResidueField
end GlobalTheory
