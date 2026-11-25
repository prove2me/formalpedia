-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rho_zero_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:05.914859+00:00
-- url     : https://prove2.me/submissions/dc9a3ff2-32f4-4dcf-9e9f-5f8df575e9bf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_e_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowDeriv_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rhoDeriv_zero_E

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
theorem _root_.solution (i j : Fin n) : rho 0 (e (i, j)) = rowOp i j := by
  refine LinearMap.ext fun f => ?_
  rw [rho_e_apply, rhoDeriv_zero_E, rowDeriv_apply]
end GroundTheory.Automorphic.HarishChandra
