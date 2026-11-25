-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.permCoord_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:27.953071+00:00
-- url     : https://prove2.me/submissions/74d6f74e-7b82-46d9-95ab-a7e2c9924a5b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SatakeSymmetric

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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (l : Fin n → ℤ) : permCoord σ l = l ∘ σ.symm :=
  rfl
end GroundTheory.Automorphic.Spherical
