-- Prove2me | solution 1 for GlobalTheory.QFam.eis_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:04.893357+00:00
-- url     : https://prove2.me/submissions/61305054-6d7b-4a60-8c6e-94ae09d1d7e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EisensteinDeltaQExpansionIntegrality
import Theorems.Thm_GlobalTheory_QFam_eis_hasQ_int
import Theorems.Thm_GlobalTheory_QFam_eis_qAll
import Theorems.Thm_GlobalTheory_QFam_eis_qConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) →
    (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧
      ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  intro N hN F hF
  exact ⟨eis_hasQ_int N hN F hF, fun R => eis_qAll N hN F hF R, fun g => eis_qConj N hN F hF g⟩
end GlobalTheory.QFam
