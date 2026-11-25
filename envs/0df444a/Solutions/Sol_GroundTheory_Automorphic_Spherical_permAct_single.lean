-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.permAct_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:06:39.005822+00:00
-- url     : https://prove2.me/submissions/d0b1ecb2-0ba5-482d-a1d7-9cee998e9bd2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_permCoord_apply

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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) (c : ℂ) :
    permAct σ (single l c) = single (l ∘ σ.symm) c := by
  simp [permAct, mapDomainAlgHom, mapDomain_single, permCoord_apply]
end GroundTheory.Automorphic.Spherical
