-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.eq_zero_of_rho_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:26.297119+00:00
-- url     : https://prove2.me/submissions/b48b789d-580d-4f7f-830a-700df5fb9065

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_zero_of_rho_one_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_one_eq_zero_of_rho_zero_eq_zero


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
theorem _root_.solution {u : U n} (h : rho 0 u = 0) : u = 0 :=
  eq_zero_of_rho_one_eq_zero (rho_one_eq_zero_of_rho_zero_eq_zero u h)
end GroundTheory.Automorphic.HarishChandra
