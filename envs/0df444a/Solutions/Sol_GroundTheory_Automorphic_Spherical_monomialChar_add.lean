-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.monomialChar_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:43.452388+00:00
-- url     : https://prove2.me/submissions/034a7bc4-e7bd-4245-bb3f-8ce31fe471a7

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
theorem _root_.solution (l l' : Fin n → ℤ) (w : Fin n → ℂˣ) :
    monomialChar (l + l') w = monomialChar l w * monomialChar l' w := by
  simp only [monomialChar_apply, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]
end GroundTheory.Automorphic.Spherical
