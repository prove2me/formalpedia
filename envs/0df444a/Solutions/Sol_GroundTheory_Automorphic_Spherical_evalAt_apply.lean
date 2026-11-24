-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.evalAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:25:03.117701+00:00
-- url     : https://prove2.me/submissions/c364c033-c69e-459a-a6a4-20bfd7b65ea9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent

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
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (w : Fin n → ℂˣ) (p : LaurentRing n) :
    evalAt w p = p.coeff.sum fun l c => c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_apply]
  rfl
end GroundTheory.Automorphic.Spherical
