-- Prove2me | solution 1 for GlobalTheory.T.exists_int_span_generators_of_isLattice_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:48.322459+00:00
-- url     : https://prove2.me/submissions/47ec72ee-be91-4b23-a073-6ecca1484f0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntGeneratorsCardEqOfIsLatticePi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntGeneratorsCardEqOfIsLatticePiStatement
import Theorems.Thm_GlobalTheory_exists_intGenerators_card_eq_of_isLattice_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E, (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧ Submodule.span ℚ (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | exact GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi | (intros; apply GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi <;> assumption)
end _root_.GlobalTheory.T
