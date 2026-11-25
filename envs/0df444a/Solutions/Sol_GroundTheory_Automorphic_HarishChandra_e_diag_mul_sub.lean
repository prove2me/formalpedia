-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_diag_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:25.57983+00:00
-- url     : https://prove2.me/submissions/4191aa2d-25b4-457a-af45-fbb2810aca83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_sub_mul
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (k : Fin n) (a : Fin n × Fin n) :
    e (k, k) * e a - e a * e (k, k) = (rootAt a k : ℂ) • e a := by
  rw [e_mul_sub_mul]
  obtain ⟨i, j⟩ := a
  simp only [rootAt]
  by_cases hi : k = i <;> by_cases hj : k = j
  · subst hi; subst hj; simp
  · subst hi; simp [hj, Ne.symm hj]
  · subst hj; simp [hi]
  · simp [hi, hj, Ne.symm hj]
end GroundTheory.Automorphic.HarishChandra
