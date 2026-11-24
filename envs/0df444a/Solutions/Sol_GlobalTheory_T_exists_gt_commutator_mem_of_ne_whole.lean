-- Prove2me | solution 1 for GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:11.939267+00:00
-- url     : https://prove2.me/submissions/f7d49c4f-7b9f-4052-b13b-0095becc2565

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTopStatement
import Theorems.Thm_GlobalTheory_exists_lt_commutator_mem_of_ne_top


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
theorem _root_.solution : ∀ {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G), K ≠ ⊤ → ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  first | exact @GlobalTheory.exists_lt_commutator_mem_of_ne_top | exact GlobalTheory.exists_lt_commutator_mem_of_ne_top | (intros; apply GlobalTheory.exists_lt_commutator_mem_of_ne_top <;> assumption)
end _root_.GlobalTheory.T
