-- Prove2me | solution 1 for GlobalTheory.T.hodge_projection_eigenvalue_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:09.178107+00:00
-- url     : https://prove2.me/submissions/765b9b25-7047-4cc7-88e7-7540f6420055

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionEigenvalueCompat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionEigenvalueCompatStatement
import Theorems.Thm_GlobalTheory_eigenvector_mem_ker_of_ne_coord_char


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
theorem _root_.solution : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (Q : W →ₗ[ℂ] (Fin g → ℂ)), (∀ x, Q (P x) = x) →
    ∀ (O : Type) (T : O → Module.End ℂ W) (χ : O → Fin g → ℂ),
    (∀ a (x : Λ), (fun j ↦ χ a j * (x : Fin g → ℂ) j) ∈ Λ) →
    (∀ a (x y : Λ), (y : Fin g → ℂ) = (fun j ↦ χ a j * (x : Fin g → ℂ) j) → T a (P x) = P y) →
    ∀ ψ : O → ℂ, (∀ j, ∃ a, χ a j ≠ ψ a) →
    (⨅ a, Module.End.eigenspace (T a) (ψ a) : Submodule ℂ W) ≤ LinearMap.ker Q := by
  first | exact @GlobalTheory.eigenvector_mem_ker_of_ne_coord_char | exact GlobalTheory.eigenvector_mem_ker_of_ne_coord_char | (intros; apply GlobalTheory.eigenvector_mem_ker_of_ne_coord_char <;> assumption)
end _root_.GlobalTheory.T
