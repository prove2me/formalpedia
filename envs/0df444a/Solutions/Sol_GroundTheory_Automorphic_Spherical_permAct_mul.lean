-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.permAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:44.854546+00:00
-- url     : https://prove2.me/submissions/ab05fdfc-06d2-4e86-b04e-70d5a6a96a07

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
theorem _root_.solution (σ τ : Equiv.Perm (Fin n)) :
    permAct (σ * τ) = (permAct σ).comp (permAct τ) := by
  refine AddMonoidAlgebra.algHom_ext (fun l => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, permAct_single, permAct_single, permAct_single]
  congr 1
end GroundTheory.Automorphic.Spherical
