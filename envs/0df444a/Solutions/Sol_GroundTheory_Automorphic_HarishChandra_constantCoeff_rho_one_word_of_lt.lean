-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.constantCoeff_rho_one_word_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:16:28.979799+00:00
-- url     : https://prove2.me/submissions/999ea50a-0b37-4c2b-89b8-3437a8046d95

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_geDeg_anti
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_constantCoeff_eq_zero_of_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_geDeg_of_isHomogeneous
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_one_word_sub_iterPd

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
theorem _root_.solution (w : List (Fin n × Fin n)) (f : Poly n) (d : ℕ)
    (hf : f.IsHomogeneous d) (h : w.length < d) :
    constantCoeff (rho 1 (word w) f) = 0 := by
  have hf' := mem_geDeg_of_isHomogeneous hf
  have h1 := rho_one_word_sub_iterPd w h.le hf'
  have h2 := iterPd_mem_geDeg w hf'
  rw [← sub_add_cancel (rho 1 (word w) f) (iterPd w f), map_add,
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h1),
    constantCoeff_eq_zero_of_mem_geDeg (geDeg_anti (by omega) h2), add_zero]
end GroundTheory.Automorphic.HarishChandra
