-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_diag_mul_word_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:24.738828+00:00
-- url     : https://prove2.me/submissions/9d2fc1e6-f89c-419f-943a-08f355ba6261

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_diag_mul_sub
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
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
theorem _root_.solution (k : Fin n) (w : List (Fin n × Fin n)) :
    e (k, k) * word w - word w * e (k, k) = (((w.map fun a => rootAt a k).sum : ℤ) : ℂ) • word w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [word_cons, List.map_cons, List.sum_cons]
    have h1 := e_diag_mul_sub k a
    calc e (k, k) * (e a * word w) - e a * word w * e (k, k)
        = (e (k, k) * e a - e a * e (k, k)) * word w + e a * (e (k, k) * word w - word w * e (k, k)) := by
          noncomm_ring
      _ = _ := by
          rw [h1, ih, smul_mul_assoc, mul_smul_comm, ← add_smul]
          push_cast; ring_nf
end GroundTheory.Automorphic.HarishChandra
