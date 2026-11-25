-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.eq_sum_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:50.055606+00:00
-- url     : https://prove2.me/submissions/83193a61-efab-4fcf-9eb6-fe756b01b1a3

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
theorem _root_.solution (X : gl n) : X = ∑ a : Fin n × Fin n, X a.1 a.2 • E a := by
  ext i j
  simp only [E, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp
end GroundTheory.Automorphic.HarishChandra
