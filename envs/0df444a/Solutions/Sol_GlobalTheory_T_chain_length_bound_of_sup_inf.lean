-- Prove2me | solution 1 for GlobalTheory.T.chain_length_bound_of_sup_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:14.908695+00:00
-- url     : https://prove2.me/submissions/39579ee6-23f3-4544-af01-ed06796b7066

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ChainLengthBoundOfSupInf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ChainLengthBoundOfSupInfStatement
import Theorems.Thm_GlobalTheory_modular_chain_bound_add


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
theorem _root_.solution : ∀ {α : Type} [Lattice α] [IsModularLattice α] (C : α) (Q Q1 Q2 : α → Prop) (L1 L2 : ℕ),
    (∀ x, Q x → Q1 (x ⊓ C)) → (∀ x, Q x → Q2 (x ⊔ C)) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q1 (N i)) → r ≤ L1) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q2 (N i)) → r ≤ L2) →
    ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L1 + L2 := by
  first | exact @GlobalTheory.modular_chain_bound_add | exact GlobalTheory.modular_chain_bound_add | (intros; apply GlobalTheory.modular_chain_bound_add <;> assumption)
end _root_.GlobalTheory.T
