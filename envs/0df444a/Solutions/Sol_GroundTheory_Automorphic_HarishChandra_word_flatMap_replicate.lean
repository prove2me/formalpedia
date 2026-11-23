-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.word_flatMap_replicate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:54.512479+00:00
-- url     : https://prove2.me/submissions/e038f208-b02b-44c4-b2e9-52ec9a9935e3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
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



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (l : List (Fin n × Fin n)) (m : Fin n × Fin n → ℕ) :
    word (l.flatMap fun a => List.replicate (m a) a) = (l.map fun a => e a ^ m a).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, word_append, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [word, List.map_replicate, List.prod_replicate]
end GroundTheory.Automorphic.HarishChandra
