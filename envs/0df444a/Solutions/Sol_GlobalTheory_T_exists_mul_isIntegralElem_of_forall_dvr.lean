-- Prove2me | solution 1 for GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:49.104424+00:00
-- url     : https://prove2.me/submissions/145242af-99b1-4225-ba53-189f5e0a5688

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulIsIntegralElemOfForallDiscreteValuation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulIsIntegralElemOfForallDiscreteValuationStatement
import Theorems.Thm_GlobalTheory_exists_mul_isIntegralElem_of_forall_discreteValuationSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B), Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) → ∀ (p : Ideal C), p.IsPrime → ∀ f : B, (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) → ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  first | exact @GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | exact GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | (intros; apply GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring <;> assumption)
end _root_.GlobalTheory.T
