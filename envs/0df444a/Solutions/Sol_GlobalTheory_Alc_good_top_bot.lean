-- Prove2me | solution 1 for GlobalTheory.Alc.good_top_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:26.965333+00:00
-- url     : https://prove2.me/submissions/6b3a5b3a-02e3-46c4-a1bc-f93b352795b8

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_GoodTopBot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Alc
open Formalism.GradedWeylDivisibility
open MvPolynomial
namespace GlobalTheory.Alc
namespace _root_.GlobalTheory.Alc
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) :
    _root_.GlobalTheory.Alc.Good (⊤ : Submodule R (MvPolynomial (Fin r × Fin n) R)) ∧ _root_.GlobalTheory.Alc.Good (⊥ : Submodule R (MvPolynomial (Fin r × Fin n) R)) := by
  refine ⟨⟨fun _ _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top,
    fun _ _ _ => Submodule.mem_top⟩, ⟨?_, ?_, ?_⟩⟩
  · intro a b f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]
  · intro μ f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]
  · intro σ f hf
    rw [Submodule.mem_bot] at hf ⊢
    simp [hf]
end _root_.GlobalTheory.Alc
end GlobalTheory.Alc
