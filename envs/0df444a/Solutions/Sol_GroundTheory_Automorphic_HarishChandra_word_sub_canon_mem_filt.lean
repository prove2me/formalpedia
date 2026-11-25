-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.word_sub_canon_mem_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:04.814933+00:00
-- url     : https://prove2.me/submissions/33b54839-4725-4d21-bac0-f02fedcb448b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_closed_true
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_sub_word_mem_of_perm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_perm_expand
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wordSpan_le_filt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (w : List (Fin n × Fin n)) :
    word w - canon (Multiset.toFinsupp (w : Multiset _)) ∈ filt (n := n) (w.length - 1) :=
  wordSpan_le_filt _ _ (word_sub_word_mem_of_perm closed_true (perm_expand w) fun _ _ => trivial)
end GroundTheory.Automorphic.HarishChandra
