-- Prove2me | solution 1 for GlobalTheory.finite_injective_localHom_and_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:03.710709+00:00
-- url     : https://prove2.me/submissions/5e7ec1dd-a129-4c68-a019-e6dece5fec09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteInjectiveRingHomIsLocalHomAndExtend
import Theorems.Thm_GlobalTheory_ValuationExtensionExistence_main


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
theorem _root_.solution (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R) :
    Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionExistence.main
  | exact _root_.GlobalTheory.ValuationExtensionExistence.main
  | (apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionExistence.main ..)
end GlobalTheory
