-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:22.1186+00:00
-- url     : https://prove2.me/submissions/d32653aa-7abe-4690-aad0-e171c754b4da

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_eq_zero_of_mem_sup
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sub_hcEmb_mem

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
theorem _root_.solution (u : U n) (p : MvPolynomial (Fin n) ℂ) :
    hcProjLin u = p ↔ u - hcEmb p ∈ nMinusU n ⊔ nPlusU n := by
  constructor
  · rintro rfl; exact sub_hcEmb_mem u
  · intro h
    have := hcProjLin_eq_zero_of_mem_sup h
    rwa [map_sub, hcProjLin_hcEmb, sub_eq_zero] at this
end GroundTheory.Automorphic.HarishChandra
