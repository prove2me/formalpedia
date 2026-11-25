-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.span_canon_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:41.583698+00:00
-- url     : https://prove2.me/submissions/9ff4dbbd-c4e1-4603-a342-c40c6fdadae9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_closed_true
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_canonSpan
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_singleton
import Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra___eq_sum_e_072213ad0100
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution : Submodule.span ℂ (Set.range (canon (n := n))) = ⊤ := by
  have hword : ∀ w : List (Fin n × Fin n), word w ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    intro w
    have := word_mem_canonSpan closed_true w (fun _ _ => trivial)
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨m, -, -, -, rfl⟩
    exact Submodule.subset_span ⟨m, rfl⟩
  set S := Submodule.span ℂ (Set.range (canon (n := n)))
  have hS : Submodule.span ℂ (Set.range (word (n := n))) ≤ S :=
    Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact hword w)
  have hall : ∀ u : U n, u ∈ Submodule.span ℂ (Set.range (word (n := n))) := by
    intro u
    induction u using U.induction with
    | halg r =>
      rw [Algebra.algebraMap_eq_smul_one, ← word_nil]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
    | hι X =>
      rw [ι_eq_sum_e]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
      rw [← word_singleton]
      exact Submodule.subset_span ⟨[a], rfl⟩
    | hmul a b ha hb =>
      have : Submodule.span ℂ (Set.range (word (n := n))) *
          Submodule.span ℂ (Set.range (word (n := n))) ≤
            Submodule.span ℂ (Set.range (word (n := n))) := by
        rw [Submodule.span_mul_span]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨v ++ w, word_append v w⟩
      exact this (Submodule.mul_mem_mul ha hb)
    | hadd a b ha hb => exact Submodule.add_mem _ ha hb
  exact eq_top_iff.2 fun u _ => hS (hall u)
end GroundTheory.Automorphic.HarishChandra
