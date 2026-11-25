-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.E_mul_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:53.980019+00:00
-- url     : https://prove2.me/submissions/e89ee62b-c678-460f-8e1a-ed59f887a82d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (a b : Fin n × Fin n) :
    E a * E b - E b * E a =
      (if a.2 = b.1 then E (a.1, b.2) else 0) - (if b.2 = a.1 then E (b.1, a.2) else 0) := by
  obtain ⟨i, j⟩ := a
  obtain ⟨k, l⟩ := b
  simp only [E]
  congr 1
  · by_cases h : j = k
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]
  · by_cases h : l = i
    · subst h; simp [Matrix.single_mul_single_same]
    · simp [h, Matrix.single_mul_single_of_ne (h := h)]
end GroundTheory.Automorphic.HarishChandra
