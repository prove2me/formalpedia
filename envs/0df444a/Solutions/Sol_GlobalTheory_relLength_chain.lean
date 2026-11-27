-- Prove2me | solution 1 for GlobalTheory.relLength_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:38.106425+00:00
-- url     : https://prove2.me/submissions/7a294039-f5f9-44bb-adf5-ef8587d10ae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableIffOfLeOfLe
import Theorems.Thm_GlobalTheory_lengthCommensurable_equivalence
import Theorems.Thm_GlobalTheory_LengthCommensurable_inf_right
import Theorems.Thm_GlobalTheory_LengthCommensurable_sup_right
import Theorems.Thm_GlobalTheory_LengthCommensurable_inf
import Theorems.Thm_GlobalTheory_LengthCommensurable_sup
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_eq_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory
theorem _root_.solution :
    (∀ A B C : Submodule R V, C ≤ B → B ≤ A → relLength A C = relLength A B + relLength B C) ∧
    (∀ A B C : Submodule R V, relLength A C ≤ relLength A B + relLength B C) ∧
    Equivalence (LengthCommensurable : Submodule R V → Submodule R V → Prop) ∧
    (∀ A B C : Submodule R V, LengthCommensurable A B → LengthCommensurable A C →
      LengthCommensurable A (B ⊓ C) ∧ LengthCommensurable A (B ⊔ C)) ∧
    (∀ A A' B B' : Submodule R V, LengthCommensurable A A' → LengthCommensurable B B' →
      LengthCommensurable (A ⊓ B) (A' ⊓ B') ∧ LengthCommensurable (A ⊔ B) (A' ⊔ B')) ∧
    (∀ A B C : Submodule R V, LengthCommensurable A B → LengthCommensurable B C →
      signedLength A C = signedLength A B + signedLength B C) :=
  ⟨fun _ _ _ => relLength_eq_add_of_le, relLength_le_add, lengthCommensurable_equivalence,
    fun _ _ _ h₁ h₂ => ⟨h₁.inf_right h₂, h₁.sup_right h₂⟩,
    fun _ _ _ _ h₁ h₂ => ⟨h₁.inf h₂, h₁.sup h₂⟩,
    fun _ _ _ => LengthCommensurable.signedLength_eq_add⟩
end GlobalTheory
