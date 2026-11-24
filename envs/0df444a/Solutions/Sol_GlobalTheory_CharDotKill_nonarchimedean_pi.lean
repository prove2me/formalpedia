-- Prove2me | solution 1 for GlobalTheory.CharDotKill.nonarchimedean_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:45.53114+00:00
-- url     : https://prove2.me/submissions/67e86b91-70d4-4b7b-87d5-6e0860388cca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CharDotKill
namespace GlobalTheory.CharDotKill
theorem _root_.solution {κ K : Type} [Finite κ] [AddCommGroup K] [TopologicalSpace K]
    [NonarchimedeanAddGroup K] : NonarchimedeanAddGroup (κ → K) where
  is_nonarchimedean S hS := by
    rw [nhds_pi, Filter.mem_pi] at hS
    obtain ⟨I, -, t, ht, hsub⟩ := hS
    choose M hM using fun i => NonarchimedeanAddGroup.is_nonarchimedean _ (ht i)
    refine ⟨⟨AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup, ?_⟩, ?_⟩
    · change IsOpen ((AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup : AddSubgroup (κ → K)) : Set (κ → K))
      rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (M i).isOpen
    · intro x hx
      apply hsub
      intro i _
      exact hM i (hx i (Set.mem_univ i))
end GlobalTheory.CharDotKill
