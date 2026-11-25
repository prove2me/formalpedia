-- Prove2me | solution 1 for GlobalTheory.QFam.eis_qAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:07:46.573882+00:00
-- url     : https://prove2.me/submissions/ac8f5f8d-bd9c-4705-8a14-5b2ca3569c38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EisensteinDeltaQExpansionIntegrality
import Theorems.Thm_GlobalTheory_QFam_eis_hasQ_int

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
theorem _root_.solution (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD)
    (R : Subring ℂ) : QAll (· ∈ R) N F := by
  obtain ⟨a, ha⟩ := eis_hasQ_int N hN F hF
  exact ⟨_, ha, fun n => intCast_mem R (a n)⟩
end GlobalTheory.QFam
