-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_mem_nPlusU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:41:48.847399+00:00
-- url     : https://prove2.me/submissions/9f8ae7dd-cfba-4a25-9608-c6ea3e8c3eb7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_upL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_of_mem_blockW
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_ne_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_blocks
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_singleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
open scoped IsMulCommutative
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) : canon m ∈ nPlusU n := by
  obtain ⟨a, ha, hm⟩ := h
  have hne := blockW_ne_nil (mem_upL.2 ha) hm
  rw [canon_eq_blocks, ← List.dropLast_append_getLast hne, word_append, word_singleton, ← mul_assoc]
  refine Submodule.subset_span ⟨_, _, ?_, rfl⟩
  exact mem_upL.1 (mem_of_mem_blockW (List.getLast_mem hne)).1
end GroundTheory.Automorphic.HarishChandra
