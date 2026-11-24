-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_generating_operator_stable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:41.657235+00:00
-- url     : https://prove2.me/submissions/3640fab7-3e44-43d8-b12b-bbdd005e1a67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBoundedStatement
import Theorems.Thm_GlobalTheory_StabGen_exists_finset_generating


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  first | exact @GlobalTheory.StabGen.exists_finset_generating | exact GlobalTheory.StabGen.exists_finset_generating | (intros; apply GlobalTheory.StabGen.exists_finset_generating <;> assumption)
end _root_.GlobalTheory.T
