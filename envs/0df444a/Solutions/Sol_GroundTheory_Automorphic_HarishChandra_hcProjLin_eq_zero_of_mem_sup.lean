-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_zero_of_mem_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:44:45.995858+00:00
-- url     : https://prove2.me/submissions/33f507a9-1d62-4309-9d3b-a5ebefd5abeb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_eq_zero_of_mem_nMinusU

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
theorem _root_.solution {x : U n} (hx : x ∈ nMinusU n ⊔ nPlusU n) :
    hcProjLin x = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, hcProjLin_eq_zero_of_mem_nMinusU hy, hcProjLin_eq_zero_of_mem_nPlusU hz, add_zero]
end GroundTheory.Automorphic.HarishChandra
