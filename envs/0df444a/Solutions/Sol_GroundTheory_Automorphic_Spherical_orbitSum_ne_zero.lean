-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.orbitSum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:37.196269+00:00
-- url     : https://prove2.me/submissions/c60e799f-a12c-4908-b082-5c554834003f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric
import Theorems.Thm_GroundTheory_Automorphic_Spherical_coeff_orbitSum_self_ne_zero

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
theorem _root_.solution (ν : Fin n → ℤ) : orbitSum ν ≠ 0 := fun h =>
  coeff_orbitSum_self_ne_zero ν (by rw [h]; rfl)
end GroundTheory.Automorphic.Spherical
