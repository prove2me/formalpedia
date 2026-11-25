-- Prove2me | solution 1 for GlobalTheory.T.eisenstein_delta_qExpansion_integrality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:02.58121+00:00
-- url     : https://prove2.me/submissions/bdc5ed8c-d2f4-48cb-8891-7090b69870f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EisensteinDeltaQExpansionIntegrality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EisensteinDeltaQExpansionIntegralityStatement
import Theorems.Thm_GlobalTheory_QFam_eis_q


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) → (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧ ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  first | exact @GlobalTheory.QFam.eis_q | exact GlobalTheory.QFam.eis_q | (intros; apply GlobalTheory.QFam.eis_q <;> assumption)
end _root_.GlobalTheory.T
