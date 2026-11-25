-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.harishChandraHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:31.428713+00:00
-- url     : https://prove2.me/submissions/c318e1e5-529b-4a97-a310-d7817513b54b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_injOn_center
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_injective
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_harishChandraHom_apply


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
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution : Function.Injective (harishChandraHom (n := n)) := by
  intro z z' h
  rw [harishChandraHom_apply, harishChandraHom_apply] at h
  exact Subtype.ext (hcProjLin_injOn_center z.2 z'.2 (translate_injective _ h))
end GroundTheory.Automorphic.HarishChandra
