-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rho_one_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:37.68869+00:00
-- url     : https://prove2.me/submissions/58cac2a6-ff15-48c4-87a7-e038cd35fd35

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra_rho___apply_861919892aea
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rhoDeriv_one_shift
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (u : U n) (f : Poly n) : rho 1 u (shift f) = shift (rho 0 u f) := by
  induction u using U.induction generalizing f with
  | halg r => simp [AlgHom.commutes, Module.algebraMap_end_apply]
  | hι M => rw [rho_ι_apply, rho_ι_apply, rhoDeriv_one_shift]
  | hmul a b ha hb => rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha]
  | hadd a b ha hb => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb,
      map_add]
end GroundTheory.Automorphic.HarishChandra
