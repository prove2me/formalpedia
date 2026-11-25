-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rho_one_eq_zero_of_rho_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:44.65457+00:00
-- url     : https://prove2.me/submissions/0f450aaa-35a1-40bb-8338-6d9dace85530

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_one_shift

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
theorem _root_.solution (u : U n) (h : rho 0 u = 0) : rho 1 u = 0 := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨g, rfl⟩ := (shift : Poly n ≃ₐ[ℂ] Poly n).surjective f
  rw [rho_one_shift, h, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
end GroundTheory.Automorphic.HarishChandra
