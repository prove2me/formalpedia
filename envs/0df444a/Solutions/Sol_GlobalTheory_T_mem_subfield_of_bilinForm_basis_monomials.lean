-- Prove2me | solution 1 for GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:29.835313+00:00
-- url     : https://prove2.me/submissions/5cf3faa8-0d2c-469b-a981-664647cc0956

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomialsStatement
import Theorems.Thm_GlobalTheory_mem_subfield_of_bilinForm_monomials


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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  first | exact @GlobalTheory.mem_subfield_of_bilinForm_monomials | exact GlobalTheory.mem_subfield_of_bilinForm_monomials | (intros; apply GlobalTheory.mem_subfield_of_bilinForm_monomials <;> assumption)
end _root_.GlobalTheory.T
