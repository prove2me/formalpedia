-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.conjU_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:16.670561+00:00
-- url     : https://prove2.me/submissions/960b22d1-fd79-4970-b8e6-663320dc7a1d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_conjU_conjU_inv

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
theorem _root_.solution {g : (gl n)ˣ} {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    conjU g z ∈ Subalgebra.center ℂ (U n) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro u
  rw [← conjU_conjU_inv g u, ← map_mul, ← map_mul, hz]
end GroundTheory.Automorphic.HarishChandra
