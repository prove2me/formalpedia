-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.evalAt_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:15:14.792141+00:00
-- url     : https://prove2.me/submissions/8eff0394-d0ef-4876-917c-9a81f553bf9e

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
theorem _root_.solution (w : Fin n → ℂˣ) (l : Fin n → ℤ) (c : ℂ) :
    evalAt w (single l c) = c * monomialChar l w := by
  rw [evalAt, AddMonoidAlgebra.lift_single, smul_eq_mul]
  rfl
end GroundTheory.Automorphic.Spherical
