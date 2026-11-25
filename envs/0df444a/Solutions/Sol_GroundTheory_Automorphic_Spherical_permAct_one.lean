-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.permAct_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:45.62527+00:00
-- url     : https://prove2.me/submissions/c1be8271-d72d-482f-baf4-522e96e0bb30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_permAct_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open AddMonoidAlgebra MvPolynomial
open GroundTheory.Automorphic.Spherical
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution : permAct (1 : Equiv.Perm (Fin n)) = AlgHom.id ℂ (LaurentRing n) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [permAct_single, AlgHom.id_apply]
  rfl
end GroundTheory.Automorphic.Spherical
