-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.psum_mem_polyLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:22.295378+00:00
-- url     : https://prove2.me/submissions/26155e9d-5c85-42a4-8d3e-e7c677624973

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_polyLE

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
theorem _root_.solution (k : ℕ) : psum (Fin n) ℂ k ∈ polyLE n k := by
  rw [psum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mem_polyLE]
  exact (totalDegree_pow _ _).trans (by rw [totalDegree_X, mul_one])
end GroundTheory.Automorphic.HarishChandra
