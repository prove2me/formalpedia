-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_mem_nMinusU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:43.974794+00:00
-- url     : https://prove2.me/submissions/fd60c592-1ea5-4a30-bdd9-483b9bb8623e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_lowL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_of_mem_blockW
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_ne_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_blocks
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
open scoped IsMulCommutative
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {m : Fin n × Fin n →₀ ℕ} (h : HasLower m) : canon m ∈ nMinusU n := by
  obtain ⟨a, ha, hm⟩ := h
  have hne := blockW_ne_nil (mem_lowL.2 ha) hm
  obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil hne
  rw [canon_eq_blocks, hbl, word_cons, mul_assoc, mul_assoc]
  refine Submodule.subset_span ⟨_, b, ?_, rfl⟩
  have : b ∈ blockW (lowL n) m := by rw [hbl]; exact List.mem_cons_self ..
  exact mem_lowL.1 (mem_of_mem_blockW this).1
end GroundTheory.Automorphic.HarishChandra
