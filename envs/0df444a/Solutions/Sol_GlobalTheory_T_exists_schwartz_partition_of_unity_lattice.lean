-- Prove2me | solution 1 for GlobalTheory.T.exists_schwartz_partition_of_unity_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:21:51.824698+00:00
-- url     : https://prove2.me/submissions/99db0882-86b7-4d79-b1e0-6e3167dfc72c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzPartitionOfUnityLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzPartitionOfUnityLatticeStatement
import Theorems.Thm_GlobalTheory_exists_schwartz_hasCompactSupport_latticeTranslates_sum_one


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
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  first | exact @GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one | exact GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one | (intros; apply GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one <;> assumption)
end _root_.GlobalTheory.T
