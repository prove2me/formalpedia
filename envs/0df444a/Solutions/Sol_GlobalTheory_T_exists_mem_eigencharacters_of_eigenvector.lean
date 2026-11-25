-- Prove2me | solution 1 for GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:21:27.656972+00:00
-- url     : https://prove2.me/submissions/8b158f53-490f-4fdc-9be8-34a9fe27a20c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EigencharactersFiniteOfCommutingAnnihilated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EigencharactersFiniteOfCommutingAnnihilatedStatement
import Theorems.Thm_GlobalTheory_eigencharacters_finite_of_commuting_annihilated


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
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 → (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by
  first | exact @GlobalTheory.eigencharacters_finite_of_commuting_annihilated | exact GlobalTheory.eigencharacters_finite_of_commuting_annihilated | (intros; apply GlobalTheory.eigencharacters_finite_of_commuting_annihilated <;> assumption)
end _root_.GlobalTheory.T
