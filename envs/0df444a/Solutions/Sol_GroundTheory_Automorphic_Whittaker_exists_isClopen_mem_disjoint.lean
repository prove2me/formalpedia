-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_isClopen_mem_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:08.339045+00:00
-- url     : https://prove2.me/submissions/36801b5f-5241-4b3c-8e17-a2433b9acf98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Theorems.Thm_GroundTheory_Automorphic_exists_isCompact_isOpen_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {Q : Set X} (hQ : IsCompact Q) {y : X} (hy : y ∉ Q) :
    ∃ V : Set X, IsClopen V ∧ y ∈ V ∧ Disjoint V Q := by
  obtain ⟨V, hVc, hVo, hyV, hVQ⟩ :=
    exists_isCompact_isOpen_subset (hQ.isClosed.isOpen_compl.mem_nhds hy)
  exact ⟨V, ⟨hVc.isClosed, hVo⟩, hyV, Set.subset_compl_iff_disjoint_right.mp hVQ⟩
end GroundTheory.Automorphic.Whittaker
