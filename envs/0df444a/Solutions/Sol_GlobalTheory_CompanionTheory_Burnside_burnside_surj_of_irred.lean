-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:13.130688+00:00
-- url     : https://prove2.me/submissions/e3ef6c7d-5aac-4013-9541-e364a0d142d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BurnsideSurjOfIrred
import Theorems.Thm_GlobalTheory_CompanionTheory_Burnside_mem_of_irred

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Burnside
namespace GlobalTheory.CompanionTheory.Burnside
theorem _root_.solution {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  intro f
  have h := mem_of_irred ρ.range (fun N hN => hirr N fun a w hw => hN (ρ a) ⟨a, rfl⟩ w hw) f
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩
end GlobalTheory.CompanionTheory.Burnside
