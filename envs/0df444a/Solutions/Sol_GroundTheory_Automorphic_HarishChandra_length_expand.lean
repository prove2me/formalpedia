-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.length_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:43.313672+00:00
-- url     : https://prove2.me/submissions/11f30583-e5e9-4ff3-b7ae-8e679e94638a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_letters
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nodup_letters
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
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) : (expand m).length = m.degree := by
  rw [Finsupp.degree_eq_sum, expand, List.length_flatMap]
  simp only [List.length_replicate]
  have : (letters n).toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun a => List.mem_toFinset.2 (mem_letters a)
  rw [← this, List.sum_toFinset _ nodup_letters]
end GroundTheory.Automorphic.HarishChandra
