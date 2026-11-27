-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.spanLower_le_nMinusU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:10.57205+00:00
-- url     : https://prove2.me/submissions/be645353-96bc-41a6-9f44-3a88e8d9d24f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_nMinusU

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
open scoped IsMulCommutative
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution : spanLower n ≤ nMinusU n :=
  Submodule.span_le.2 fun _ ⟨_, h, hx⟩ => hx ▸ canon_mem_nMinusU h
end GroundTheory.Automorphic.HarishChandra
