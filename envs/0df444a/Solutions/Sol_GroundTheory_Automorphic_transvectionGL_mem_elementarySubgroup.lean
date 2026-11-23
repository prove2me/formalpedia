-- Prove2me | solution 1 for GroundTheory.Automorphic.transvectionGL_mem_elementarySubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:59.136386+00:00
-- url     : https://prove2.me/submissions/dd4662cf-f2f7-4712-a76f-d7ac1e68f0f4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary

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
theorem _root_.solution (t : TransvectionStruct n R) :
    transvectionGL n R t ∈ elementarySubgroup n R :=
  Subgroup.subset_closure ⟨t, rfl⟩
end GroundTheory.Automorphic
