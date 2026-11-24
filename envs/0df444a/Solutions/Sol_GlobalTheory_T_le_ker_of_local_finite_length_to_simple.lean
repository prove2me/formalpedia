-- Prove2me | solution 1 for GlobalTheory.T.le_ker_of_local_finite_length_to_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:26.211196+00:00
-- url     : https://prove2.me/submissions/139054b9-3247-4aff-b2b6-cd87b2dc9f6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Theorems.Thm_GlobalTheory_TensHead_le_ker_of_simple_commuting


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
theorem _root_.solution : ∀ {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab Op K → Rel ≤ LinearMap.ker φ →
    (∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ) →
    (∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g) →
    (∀ U : Submodule ℂ W, GlobalTheory.TensHead.Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) →
    K ≤ LinearMap.ker φ := by
  first | exact @GlobalTheory.TensHead.le_ker_of_simple_commuting | exact GlobalTheory.TensHead.le_ker_of_simple_commuting | (intros; apply GlobalTheory.TensHead.le_ker_of_simple_commuting <;> assumption)
end _root_.GlobalTheory.T
