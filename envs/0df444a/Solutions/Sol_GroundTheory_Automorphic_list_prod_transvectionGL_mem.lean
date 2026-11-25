-- Prove2me | solution 1 for GroundTheory.Automorphic.list_prod_transvectionGL_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:58.899294+00:00
-- url     : https://prove2.me/submissions/46355b7c-5bfe-4492-a900-f8d7683b5ee9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
import Theorems.Thm_GroundTheory_Automorphic_transvectionGL_mem_elementarySubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}
namespace GroundTheory.Automorphic
theorem _root_.solution (L : List (TransvectionStruct n R)) :
    (L.map (transvectionGL n R)).prod ∈ elementarySubgroup n R :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact transvectionGL_mem_elementarySubgroup t
end GroundTheory.Automorphic
