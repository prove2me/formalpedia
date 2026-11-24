-- Prove2me | solution 1 for GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:58.784429+00:00
-- url     : https://prove2.me/submissions/41ce19e8-181d-468e-aad1-11d3cf1290ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzPartitionOfUnityLattice
import Theorems.Thm_GlobalTheory_LatticeSumOne_exists_schwartz_lattice_sum_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  intro V _ _ _ Λ _ _
  exact LatticeSumOne.exists_schwartz_lattice_sum_one Λ
end GlobalTheory
