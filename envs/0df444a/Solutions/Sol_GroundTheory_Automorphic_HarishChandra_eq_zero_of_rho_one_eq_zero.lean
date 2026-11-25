-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.eq_zero_of_rho_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:40.309581+00:00
-- url     : https://prove2.me/submissions/0ed805e4-baff-47a3-a752-82872425fdb9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_repr_canon

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
theorem _root_.solution {u : U n} (h : rho 1 u = 0) : u = 0 := by
  rw [← sum_repr_canon u] at h ⊢
  have := coeff_eq_zero_of_rho_one _ _ h
  exact Finset.sum_eq_zero fun m hm => by rw [this m hm, zero_smul]
end GroundTheory.Automorphic.HarishChandra
