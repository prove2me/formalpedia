-- Prove2me | solution 1 for GlobalTheory.T.induced_one_sub_index_mem_degreeOneCharacterDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:14:54.172243+00:00
-- url     : https://prove2.me/submissions/483c5ced-c919-4396-abf3-fb14ff2435a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiffStatement
import Theorems.Thm_GlobalTheory_BrauerZero_ind_one_sub_index_mem_D0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] [Finite G] (K : Subgroup G), (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) → ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  first | exact @GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0 | exact GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0 | (intros; apply GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0 <;> assumption)
end _root_.GlobalTheory.T
