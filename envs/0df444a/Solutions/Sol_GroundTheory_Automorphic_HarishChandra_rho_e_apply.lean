-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rho_e_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:00.453177+00:00
-- url     : https://prove2.me/submissions/b5dc0eb4-184e-4e85-a0e2-95bdceefad71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra_rho___apply_861919892aea

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
theorem _root_.solution (c : Matrix (Fin n) (Fin n) ℂ) (a : Fin n × Fin n) (f : Poly n) :
    rho c (e a) f = rhoDeriv c (E a) f :=
  rho_ι_apply c (E a) f
end GroundTheory.Automorphic.HarishChandra
