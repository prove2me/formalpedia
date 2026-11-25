-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_mul_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:58.755052+00:00
-- url     : https://prove2.me/submissions/0f1018f5-cb22-4cbe-9571-982cff4798e5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_E_mul_sub_mul__63bac1
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
    e a * e b - e b * e a =
      (if a.2 = b.1 then e (a.1, b.2) else 0) - (if b.2 = a.1 then e (b.1, a.2) else 0) := by
  have h := congrArg (UniversalEnvelopingAlgebra.ι ℂ (L := gl n)) (E_mul_sub_mul a b)
  rw [← LieRing.of_associative_ring_bracket, LieHom.map_lie, LieRing.of_associative_ring_bracket]
    at h
  simp only [e] at h ⊢
  rw [h, map_sub]
  congr 1 <;> split_ifs <;> simp
end GroundTheory.Automorphic.HarishChandra
