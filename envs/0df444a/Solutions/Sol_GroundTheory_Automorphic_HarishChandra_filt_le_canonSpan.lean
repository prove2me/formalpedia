-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.filt_le_canonSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:42.7261+00:00
-- url     : https://prove2.me/submissions/36f387a1-1447-4606-8b84-3aefd414de71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_closed_true
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canonSpan_mono
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_canonSpan

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
theorem _root_.solution (d : ℕ) : filt (n := n) d ≤ canonSpan (fun _ => True) 0 d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, hw, rfl⟩
  exact canonSpan_mono (Nat.zero_le _) hw (word_mem_canonSpan closed_true w fun _ _ => trivial)
end GroundTheory.Automorphic.HarishChandra
