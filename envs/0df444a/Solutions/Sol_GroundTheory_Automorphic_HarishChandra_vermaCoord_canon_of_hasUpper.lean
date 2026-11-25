-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.vermaCoord_canon_of_hasUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:41.619251+00:00
-- url     : https://prove2.me/submissions/8ebdd518-71f2-4a57-a26e-7e354b9fd078

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (lam : Fin n → ℂ) {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) :
    vermaCoord lam (canon m) = 0 := by
  rw [vermaCoord, ← pbw_apply, Module.Basis.constr_basis, if_pos h]
end GroundTheory.Automorphic.HarishChandra
