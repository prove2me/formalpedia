-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mul_C_mem_polyLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:35.529824+00:00
-- url     : https://prove2.me/submissions/50f030a9-5e9a-4fe4-b011-1865914d8846

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
theorem _root_.solution {d : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ polyLE n d) (a : ℂ) :
    p * C a ∈ polyLE n d := by
  rw [mem_polyLE] at *
  exact (totalDegree_mul p (C a)).trans (by rw [totalDegree_C]; omega)
end GroundTheory.Automorphic.HarishChandra
