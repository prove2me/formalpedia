-- Prove2me | solution 1 for GlobalTheory.adicCompletion_map_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:16.014179+00:00
-- url     : https://prove2.me/submissions/4baba0df-ef2e-4f18-a71b-4021d75c4447

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapSubApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionMapInvariants
import Theorems.Thm_GlobalTheory_LinearMapDifferenceFormula_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open AdicCompletion
namespace GlobalTheory
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first
  | exact @_root_.GlobalTheory.LinearMapDifferenceFormula.main
  | exact _root_.GlobalTheory.LinearMapDifferenceFormula.main
  | (apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearMapDifferenceFormula.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearMapDifferenceFormula.main ..)
end GlobalTheory
